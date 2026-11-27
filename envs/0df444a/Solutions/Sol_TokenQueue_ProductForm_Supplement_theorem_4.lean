-- Prove2me | solution 1 for TokenQueue.ProductForm.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:44.60359+00:00
-- url     : https://prove2.me/submissions/97de3e09-d617-4b1e-b6ca-d62f49bb2b69

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_TokenQueue_ProductForm_Model
import Definitions.Def_TokenQueue_ProductForm_Supplement_CustomerChain

open TokenQueue
open TokenQueue.ProductForm
open TokenQueue.ProductForm.Supplement

open Finset

/-- **Theorem 4**, p. 10. For complex `z_c` with `|z_c| < 1`, the joint PGF
`E[∏_c z_c^{M^{(c)}}]` of the numbers of customers per type under any stationary law `Q` of the
customer-level chain is the series (19), `G` being the conditional law under `Q` of the token
holders' types given the descriptor. -/
theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) (Q : CState C T → ℝ) (hQ : IsStationaryLaw P Q)
    (z : C → ℂ) (hz : ∀ c, ‖z c‖ < 1) :
    HasSum (fun x : State T => (commonFactor P x.1 : ℂ) *
        (∑ cs : Fin x.1.length → C, (Gcond Q x.1 (List.ofFn cs) : ℂ) * ∏ j, z (cs j)) *
        ∏ j : Fin x.1.length,
          ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
            ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2)
      (∑' y, (Q y : ℂ) * ∏ c, z c ^ Mtot y c) := by
        have L12M : (∀ y, HasSum (crate P y) (lamTot P + P.eta y.length * kfun P (heldToks y))) ∧
          (∀ (A : ℕ → Finset (CState C T)) (hA : ∀ n y, y ∈ A n ↔ y.length = n), ∀ n y, ∑ y' ∈ A n, crate P y y' = (if n = y.length + 1 then lamTot P else 0) +
            if n + 1 = y.length then P.eta y.length * kfun P (heldToks y) else 0) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          have hflat : ∀ (ι : Type) (w : CState C T × Option ℕ × ℝ → ℝ)
              (g : ι → List (CState C T × Option ℕ × ℝ)) (l : List ι),
              ((l.flatMap g).map w).sum = (l.map (fun i => ((g i).map w).sum)).sum := by
            intro ι w g l
            induction l with
            | nil => rfl
            | cons a l ih =>
              rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]
          have hpass : ∀ (t : T) (l : CState C T), (passToken P t l).length = l.length := by
            intro t l
            induction l with
            | nil => rfl
            | cons a l ih =>
              obtain ⟨c, o⟩ := a
              cases o with
              | none =>
                by_cases h : t ∈ P.tok c
                · simp only [passToken, if_pos h, List.length_cons]
                · simp only [passToken, if_neg h, List.length_cons, ih]
              | some u => simp only [passToken, List.length_cons, ih]
          have harr : ∀ (y : CState C T) (f : ℕ → ℝ) (c : C),
              (((if P.tok c ⊆ held y then [(y ++ [(c, (none : Option T))], (none : Option ℕ), P.lam c)]
                else (P.tok c \ held y).toList.map fun t =>
                  (y ++ [(c, some t)], (none : Option ℕ), P.lam c * P.assign c (held y) t)).map
                (fun e => f e.1.length * e.2.2)).sum) = f (y.length + 1) * P.lam c := by
            intro y f c
            by_cases h : P.tok c ⊆ held y
            · rw [if_pos h]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
                List.length_append, List.length_cons, List.length_nil, zero_add]
            · rw [if_neg h, List.map_map]
              have hne : (P.tok c \ held y).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro h0
                exact h (Finset.sdiff_eq_empty_iff_subset.mp h0)
              have h5 := hS.2.2.2.2.1 c (held y) hne
              rw [Finset.sum_map_toList, ← mul_one (f (y.length + 1) * P.lam c), ← h5, Finset.mul_sum]
              refine Finset.sum_congr rfl (fun t _ => ?_)
              simp only [Function.comp, List.length_append, List.length_cons, List.length_nil, zero_add]
              ring
          have hdep : ∀ (y : CState C T) (f : ℕ → ℝ) (i : Fin y.length),
              ((match (y.get i).2 with
                | none => []
                | some t => [(passToken P t (y.eraseIdx i), some i.val, depRate P y i.val)]).map
                (fun e : CState C T × Option ℕ × ℝ => f e.1.length * e.2.2)).sum =
              f (y.length - 1) * depRate P y i.val := by
            intro y f i
            have hg : y[i.val]? = some (y.get i) := by simp
            rcases hv : y.get i with ⟨c, o⟩
            rw [hv] at hg
            cases o with
            | none =>
              have : depRate P y i.val = 0 := by unfold depRate; rw [hg]
              rw [this]; simp
            | some t =>
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hpass,
                List.length_eraseIdx, i.isLt, if_true]
          have hk0 : ∀ (l : List T) (t : T), kfun P (l ++ [t]) = kfun P l + P.s (l ++ [t]) := by
            intro l t
            unfold kfun
            rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
            congr 1
            · refine Finset.sum_congr rfl (fun j hj => ?_)
              rw [List.take_append_of_le_length (Nat.succ_le_of_lt (Finset.mem_range.mp hj))]
            · rw [List.take_of_length_le (by simp)]
          have hr : ∀ (e : ℝ) (y : CState C T), ∑ i ∈ range y.length,
              (match y[i]? with
                | some (_, some _) => e * P.s (heldToks (y.take (i + 1)))
                | _ => 0) = e * kfun P (heldToks y) := by
            intro e y
            induction y using List.reverseRecOn with
            | nil => simp [kfun, heldToks]
            | append_singleton y a ih =>
              rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
              have hfirst : ∑ i ∈ range y.length,
                  (match (y ++ [a])[i]? with
                    | some (_, some _) => e * P.s (heldToks ((y ++ [a]).take (i + 1)))
                    | _ => 0) = e * kfun P (heldToks y) := by
                rw [← ih]
                refine Finset.sum_congr rfl (fun i hi => ?_)
                have hi' := Finset.mem_range.mp hi
                rw [List.getElem?_append_left hi',
                  List.take_append_of_le_length (Nat.succ_le_of_lt hi')]
              rw [hfirst]
              have hlast : (y ++ [a])[y.length]? = some a := by simp
              have htk : (y ++ [a]).take (y.length + 1) = y ++ [a] :=
                List.take_of_length_le (by simp)
              rw [hlast, htk]
              obtain ⟨c, o⟩ := a
              cases o with
              | none =>
                have : heldToks (y ++ [(c, (none : Option T))]) = heldToks y := by simp [heldToks]
                rw [this]; simp
              | some t =>
                have : heldToks (y ++ [(c, some t)]) = heldToks y ++ [t] := by simp [heldToks]
                rw [this, hk0]; ring
          have hdr : ∀ (y : CState C T), ((List.finRange y.length).map
              (fun i => depRate P y i.val)).sum = P.eta y.length * kfun P (heldToks y) := by
            intro y
            rw [← hr (P.eta y.length) y, ← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_range]
            rfl
          have hc : ∀ (y : CState C T) (f : ℕ → ℝ),
              ((ctrans P y).map (fun e => f e.1.length * e.2.2)).sum =
                f (y.length + 1) * lamTot P +
                  f (y.length - 1) * (P.eta y.length * kfun P (heldToks y)) := by
            intro y f
            unfold ctrans
            simp only []
            rw [List.map_append, List.sum_append, hflat, hflat]
            congr 1
            · rw [List.map_congr_left (fun c _ => harr y f c), Finset.sum_map_toList, ← Finset.mul_sum]
              rfl
            · refine (congrArg List.sum (List.map_congr_left (fun i _ => hdep y f i))).trans ?_
              rw [List.sum_map_mul_left, hdr]
          constructor
          · skip
            have hs : ∀ L : List (CState C T × Option ℕ × ℝ),
                HasSum (fun y' => ((L.filter (fun e => e.1 = y')).map fun e => e.2.2).sum)
                  (L.map (fun e => e.2.2)).sum := by
              intro L
              induction L with
              | nil => simpa using (hasSum_zero : HasSum (fun _ : CState C T => (0 : ℝ)) 0)
              | cons a L ih =>
                have ha : HasSum (fun y' => if y' = a.1 then a.2.2 else 0) a.2.2 := hasSum_ite_eq _ _
                rw [List.map_cons, List.sum_cons]
                have hfe : (fun y' => (((a :: L).filter (fun e => e.1 = y')).map fun e => e.2.2).sum) =
                    fun y' => (if y' = a.1 then a.2.2 else 0) +
                      ((L.filter (fun e => e.1 = y')).map fun e => e.2.2).sum := by
                  funext y'
                  by_cases h : a.1 = y'
                  · rw [List.filter_cons_of_pos (by simpa using h), if_pos h.symm, List.map_cons,
                      List.sum_cons]
                  · rw [List.filter_cons_of_neg (by simpa using h), if_neg (fun h' => h h'.symm), zero_add]
                rw [hfe]
                exact ha.add ih
            intro y
            have h := hs (ctrans P y)
            have h2 := hc y (fun _ => 1)
            simp only [one_mul] at h2
            rw [h2] at h
            exact h
          · intro A hA
            have hs : ∀ (n : ℕ) (L : List (CState C T × Option ℕ × ℝ)),
                ∑ y' ∈ A n, ((L.filter (fun e => e.1 = y')).map fun e => e.2.2).sum =
                  (L.map (fun e => (if e.1.length = n then (1 : ℝ) else 0) * e.2.2)).sum := by
              intro n L
              induction L with
              | nil => simp
              | cons a L ih =>
                have hfe : ∀ y' ∈ A n,
                    (((a :: L).filter (fun e => e.1 = y')).map fun e => e.2.2).sum =
                      (if a.1 = y' then a.2.2 else 0) +
                      ((L.filter (fun e => e.1 = y')).map fun e => e.2.2).sum := by
                  intro y' _
                  by_cases h : a.1 = y'
                  · rw [List.filter_cons_of_pos (by simpa using h), if_pos h, List.map_cons,
                      List.sum_cons]
                  · rw [List.filter_cons_of_neg (by simpa using h), if_neg h, zero_add]
                rw [Finset.sum_congr rfl hfe, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons,
                  Finset.sum_ite_eq]
                congr 1
                by_cases h : a.1.length = n
                · rw [if_pos ((hA n a.1).mpr h), if_pos h, one_mul]
                · rw [if_neg (fun h' => h ((hA n a.1).mp h')), if_neg h, zero_mul]
            intro n y
            refine (hs n (ctrans P y)).trans ?_
            have h2 := hc y (fun m => if m = n then 1 else 0)
            rw [h2]
            congr 1
            · by_cases h : y.length + 1 = n
              · rw [if_pos h, if_pos h.symm, one_mul]
              · rw [if_neg h, if_neg (fun h' => h h'.symm), zero_mul]
            · by_cases h0 : y.length = 0
              · have hy : y = [] := List.length_eq_zero_iff.mp h0
                subst hy
                simp [kfun, heldToks]
              · by_cases h : n + 1 = y.length
                · rw [if_pos h, if_pos (by omega), one_mul]
                · rw [if_neg h, if_neg (by omega), zero_mul]
        have L1 := L12M.1
        have L2 := L12M.2
        have L3 : ∀ (ins : ℕ → C → T → CState C T → CState C T)
          (hins : ∀ p c t y, ins p c t y = y.take p ++ (c, some t) ::
            (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e))
          (R : CState C T → ℝ)
          (hR0 : R [] = 0)
          (hRn : ∀ y c, R (y ++ [(c, none)]) = P.lam c)
          (hRt : ∀ y c t, R (y ++ [(c, some t)]) = P.lam c * P.assign c (held y) t)
          (Inf : (CState C T → ℝ) → CState C T → ℝ)
          (hInf : ∀ f y, Inf f y = R y * f y.dropLast + ∑ p ∈ range (y.length + 1), ∑ c, ∑ t,
            P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * f (ins p c t y))
          (f : CState C T → ℝ)
          (hfv : ∀ y, ¬ Valid P y → f y = 0)
          (y : CState C T)
          (hy : Valid P y),
          HasSum (fun y' => f y' * crate P y' y) (Inf f y) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro ins hins R hR0 hRn hRt Inf hInf f hfv y hy
          have hht : ∀ a b : CState C T, heldToks (a ++ b) = heldToks a ++ heldToks b := by
            intro a b; unfold heldToks; rw [List.filterMap_append]
          have hhn : ∀ (c : C) (b : CState C T), heldToks ((c, none) :: b) = heldToks b := by
            intro c b; unfold heldToks; rfl
          have hhs : ∀ (c : C) (t : T) (b : CState C T), heldToks ((c, some t) :: b) = t :: heldToks b := by
            intro c t b; unfold heldToks; rfl
          have V1 : ∀ (a : CState C T) c b, Valid P (a ++ (c, none) :: b) → P.tok c ⊆ held a := by
            intro a c b h
            have h3 := h.2.2 a.length (by rw [List.length_append, List.length_cons]; omega)
            rw [List.getElem_append_right (le_refl _)] at h3
            simpa using h3
          have V2 : ∀ (a : CState C T) c t b, Valid P (a ++ (c, some t) :: b) → t ∈ P.tok c := by
            intro a c t b h
            have h3 := h.2.1 a.length (by rw [List.length_append, List.length_cons]; omega) t
            rw [List.getElem_append_right (le_refl _)] at h3
            simpa using h3
          have V3 : ∀ (a : CState C T) c t b, Valid P (a ++ (c, some t) :: b) →
              t ∉ heldToks a ∧ t ∉ heldToks b := by
            intro a c t b h
            have h3 := h.1
            rw [hht, hhs, List.nodup_append] at h3
            refine ⟨fun hta => h3.2.2 t hta t (List.mem_cons_self) rfl, ?_⟩
            exact (List.nodup_cons.mp h3.2.1).1
          have hp1 : ∀ (t : T) (a b : CState C T), (∀ c, (c, none) ∈ a → t ∉ P.tok c) →
              passToken P t (a ++ b) = a ++ passToken P t b := by
            intro t a b
            induction a with
            | nil => intro _; rfl
            | cons e a ih =>
              intro h
              have ih' := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                have hc := h c (List.mem_cons_self)
                simp only [List.cons_append, passToken, if_neg hc, ih']
              | some u =>
                simp only [List.cons_append, passToken, ih']
          have hu : ∀ (t : T) (b : CState C T), t ∉ heldToks b →
              b.map (fun e => if e.2 = some t then (e.1, none) else e) = b := by
            intro t b
            induction b with
            | nil => intro _; rfl
            | cons e b ih =>
              intro h
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                rw [hhn] at h
                rw [List.map_cons, ih h]; simp
              | some u =>
                rw [hhs, List.mem_cons, not_or] at h
                have hne : (some u : Option T) ≠ some t := fun hh => h.1 (Option.some.inj hh).symm
                rw [List.map_cons, ih h.2]
                simp only [if_neg hne]
          have hup : ∀ (t : T) (b : CState C T), t ∉ heldToks b →
              (passToken P t b).map (fun e => if e.2 = some t then (e.1, none) else e) = b := by
            intro t b
            induction b with
            | nil => intro _; rfl
            | cons e b ih =>
              intro h
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                rw [hhn] at h
                by_cases hc : t ∈ P.tok c
                · simp only [passToken, if_pos hc, List.map_cons, if_true]
                  rw [hu t b h]
                · simp only [passToken, if_neg hc, List.map_cons]
                  rw [ih h]; simp
              | some u =>
                rw [hhs, List.mem_cons, not_or] at h
                have hne : (some u : Option T) ≠ some t := fun hh => h.1 (Option.some.inj hh).symm
                simp only [passToken, List.map_cons, if_neg hne]
                rw [ih h.2]
          have hpu : ∀ (t : T) (b a : CState C T), Valid P (a ++ b) → t ∉ heldToks a →
              passToken P t (b.map (fun e => if e.2 = some t then (e.1, none) else e)) = b := by
            intro t b
            induction b with
            | nil => intro _ _ _; rfl
            | cons e b ih =>
              intro a hv ha
              have hv' : Valid P ((a ++ [e]) ++ b) := by
                rw [List.append_assoc, List.singleton_append]; exact hv
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                have hc : t ∉ P.tok c := fun hc => ha (List.mem_toFinset.mp (V1 a c b hv hc))
                have := ih _ hv' (by rw [hht, show heldToks [(c, (none : Option T))] = [] from rfl, List.append_nil]; exact ha)
                rw [List.map_cons]
                simp only [reduceCtorEq, if_false, passToken, if_neg hc]
                rw [this]
              | some u =>
                by_cases hut : u = t
                · subst hut
                  have h2 := V2 a c u b hv
                  rw [List.map_cons, hu u b (V3 a c u b hv).2]
                  simp only [if_true, passToken, if_pos h2]
                · have hne : (some u : Option T) ≠ some t := fun hh => hut (Option.some.inj hh)
                  have := ih _ hv' (by
                    rw [hht, hhs, List.mem_append, not_or]
                    refine ⟨ha, ?_⟩
                    rw [List.mem_cons, not_or]
                    exact ⟨fun h => hut h.symm, by simp [heldToks]⟩)
                  rw [List.map_cons]
                  simp only [if_neg hne, passToken]
                  rw [this]
          have hplen : ∀ (t : T) (b : CState C T), (passToken P t b).length = b.length := by
            intro t b
            induction b with
            | nil => rfl
            | cons e b ih =>
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                by_cases hc : t ∈ P.tok c
                · simp only [passToken, if_pos hc, List.length_cons]
                · simp only [passToken, if_neg hc, List.length_cons, ih]
              | some u => simp only [passToken, List.length_cons, ih]
          have hinslen : ∀ p c t, (ins p c t y).length = y.length + 1 := by
            intro p c t
            rw [hins, List.length_append, List.length_cons, List.length_map, List.length_take,
              List.length_drop]
            omega
          have hina : ∀ (a : CState C T) c t b, Valid P (a ++ (c, some t) :: b) →
              ∀ g, (g, none) ∈ a → t ∉ P.tok g := by
            intro a c t b hv g hg htg
            obtain ⟨u, v, rfl⟩ := List.append_of_mem hg
            have h3 := (V3 _ _ _ _ hv).1
            have h1' : Valid P (u ++ (g, none) :: (v ++ (c, some t) :: b)) := by
              simpa using hv
            have := List.mem_toFinset.mp (V1 _ _ _ h1' htg)
            exact h3 (by rw [hht]; exact List.mem_append_left _ this)
          have hkey : ∀ (a : CState C T) c t b, Valid P (a ++ (c, some t) :: b) →
              (passToken P t (a ++ b) = y ↔ a ++ (c, some t) :: b = ins a.length c t y) := by
            intro a c t b hv
            have h3 := V3 _ _ _ _ hv
            rw [hp1 t a b (hina a c t b hv), hins]
            constructor
            · intro h
              rw [← h, List.take_left, List.drop_left, hup t b h3.2]
            · intro h
              have hl : a.length < (a ++ (c, some t) :: b).length := by
                rw [List.length_append, List.length_cons]; omega
              have hl2 : a.length ≤ y.length := by
                have := congrArg List.length h
                simp only [List.length_append, List.length_cons, List.length_map, List.length_take,
                  List.length_drop] at this
                omega
              have hinj := List.append_inj h (by rw [List.length_take]; omega)
              have hb := (List.cons.inj hinj.2).2
              have hy' : Valid P (a ++ y.drop a.length) := by
                have : a ++ y.drop a.length = y := by
                  conv_lhs => rw [hinj.1]
                  have hla : (List.take a.length y).length = a.length := by rw [List.length_take]; omega
                  rw [hla, List.take_append_drop]
                rw [this]; exact hy
              rw [hb, hpu t _ a hy' h3.1]
              conv_lhs => rw [hinj.1]
              have hla : (List.take a.length y).length = a.length := by rw [List.length_take]; omega
              rw [hla, List.take_append_drop]
          have hfm : ∀ {α β : Type} (L : List α) (g : α → List β) (p : β → Bool) (h : β → ℝ),
              (((L.flatMap g).filter p).map h).sum = (L.map (fun i => (((g i).filter p).map h).sum)).sum := by
            intro α β L g p h
            induction L with
            | nil => rfl
            | cons e L ih =>
              rw [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append, ih,
                List.map_cons, List.sum_cons]
          -- departures
          have hdep : ∀ y', Valid P y' →
              (((((List.finRange y'.length).flatMap fun i =>
                match (y'.get i).2 with
                | none => []
                | some t => [(passToken P t (y'.eraseIdx i), some i.val, depRate P y' i.val)]).filter
                  (fun e => e.1 = y)).map fun e => e.2.2).sum) =
              ∑ p ∈ range (y.length + 1), ∑ c, ∑ t, if y' = ins p c t y then
                P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) else 0 := by
            intro y' hv
            rw [hfm, ← Fin.sum_univ_def]
            by_cases hlen : y'.length = y.length + 1
            · rw [← hlen, Finset.sum_range]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              obtain ⟨i, hi⟩ := i
              obtain ⟨a, e, b, hab, hal⟩ : ∃ a e b, y' = a ++ e :: b ∧ a.length = i := by
                refine ⟨y'.take i, y'[i], y'.drop (i + 1), ?_, ?_⟩
                · rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
                · rw [List.length_take]; omega
              have hge : y'.get ⟨i, hi⟩ = e := by
                subst hab; subst hal
                simp
              have hinse : ∀ c t, y' = ins i c t y → e = (c, some t) ∧ a = y.take i := by
                intro c t h
                rw [hab, hins] at h
                have hinj := List.append_inj h (by rw [List.length_take]; omega)
                exact ⟨(List.cons.inj hinj.2).1, hinj.1⟩
              obtain ⟨c0, o⟩ := e
              cases o with
              | none =>
                simp only [hge]
                rw [Finset.sum_eq_zero]
                · rfl
                · intro c _
                  refine Finset.sum_eq_zero (fun t _ => if_neg (fun h => ?_))
                  have := congrArg Prod.snd (hinse c t h).1
                  exact absurd this (by simp)
              | some t0 =>
                simp only [hge]
                have herase : y'.eraseIdx i = a ++ b := by
                  subst hab; subst hal
                  rw [List.eraseIdx_append_of_length_le (le_refl _)]
                  simp
                rw [herase]
                have hk' : (passToken P t0 (a ++ b) = y ↔ y' = ins i c0 t0 y) := by
                  have := hkey a c0 t0 b (hab ▸ hv)
                  rw [hal] at this
                  rw [hab]
                  exact this
                rw [Finset.sum_eq_single c0, Finset.sum_eq_single t0]
                · by_cases hh : y' = ins i c0 t0 y
                  · rw [if_pos hh, List.filter_cons_of_pos (by simpa using hk'.mpr hh)]
                    have ha := (hinse c0 t0 hh).2
                    have hdr : depRate P y' i = P.eta (y.length + 1) * P.s (heldToks (y.take i) ++ [t0]) := by
                      have hq : y'[i]? = some (c0, some t0) := by
                        rw [List.getElem?_eq_getElem hi]; exact congrArg some hge
                      have htk : y'.take (i + 1) = a ++ [(c0, some t0)] := by
                        rw [List.take_add_one, hq]
                        subst hal
                        rw [hab, List.take_left]; rfl
                      unfold depRate
                      rw [hq]
                      simp only
                      rw [htk, hht, hlen, ha]
                      rfl
                    simp [hdr, hlen]
                  · rw [if_neg hh, List.filter_cons_of_neg (by simpa using fun h => hh (hk'.mp h))]
                    rfl
                · intro t _ ht
                  refine if_neg (fun h => ht ?_)
                  have := congrArg Prod.snd (hinse c0 t h).1
                  exact (Option.some.inj this).symm
                · intro h; exact absurd (Finset.mem_univ _) h
                · intro c _ hc
                  refine Finset.sum_eq_zero (fun t _ => if_neg (fun h => hc ?_))
                  exact (congrArg Prod.fst (hinse c t h).1).symm
                · intro h; exact absurd (Finset.mem_univ _) h
            · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
              · intro p _
                refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun t _ => if_neg (fun h => ?_)))
                exact hlen (by rw [h, hinslen])
              · intro i _
                cases hc : (y'.get i).2 with
                | none => rfl
                | some t =>
                  simp only
                  rw [List.filter_cons_of_neg]
                  · rfl
                  · have : passToken P t (y'.eraseIdx i) ≠ y := by
                      intro h
                      have h2 := congrArg List.length h
                      rw [hplen, List.length_eraseIdx_of_lt i.2] at h2
                      have := i.2
                      omega
                    simpa using this
          -- arrivals
          have harr : ∀ y' : CState C T,
              ((((((univ : Finset C).toList.flatMap fun c =>
                if P.tok c ⊆ held y' then [(y' ++ [(c, none)], (none : Option ℕ), P.lam c)]
                else (P.tok c \ held y').toList.map fun t =>
                  (y' ++ [(c, some t)], (none : Option ℕ), P.lam c * P.assign c (held y') t))).filter
                  (fun e => e.1 = y)).map fun e => e.2.2).sum) =
              if y' = y.dropLast then R y else 0 := by
            intro y'
            rw [hfm, Finset.sum_map_toList]
            have hA : ∀ c, (((if P.tok c ⊆ held y' then [(y' ++ [(c, none)], (none : Option ℕ), P.lam c)]
                else (P.tok c \ held y').toList.map fun t =>
                  (y' ++ [(c, some t)], (none : Option ℕ), P.lam c * P.assign c (held y') t)).filter
                  (fun e => e.1 = y)).map fun e => e.2.2).sum =
                if P.tok c ⊆ held y' then (if y' ++ [(c, none)] = y then P.lam c else 0)
                else ∑ t ∈ P.tok c \ held y', if y' ++ [(c, some t)] = y then
                  P.lam c * P.assign c (held y') t else 0 := by
              intro c
              by_cases hc : P.tok c ⊆ held y'
              · rw [if_pos hc, if_pos hc]
                by_cases he : y' ++ [(c, none)] = y
                · rw [if_pos he, List.filter_cons_of_pos (by simpa using he)]
                  simp
                · rw [if_neg he, List.filter_cons_of_neg (by simpa using he)]
                  rfl
              · rw [if_neg hc, if_neg hc, ← Finset.sum_map_toList]
                generalize (P.tok c \ held y').toList = L
                induction L with
                | nil => rfl
                | cons t L ih =>
                  rw [List.map_cons, List.map_cons, List.sum_cons, ← ih]
                  by_cases he : y' ++ [(c, some t)] = y
                  · rw [if_pos he, List.filter_cons_of_pos (by simpa using he), List.map_cons,
                      List.sum_cons]
                  · rw [if_neg he, List.filter_cons_of_neg (by simpa using he), zero_add]
            rw [Finset.sum_congr rfl (fun c _ => hA c)]
            by_cases hyy : y' = y.dropLast
            · rw [if_pos hyy]
              rcases List.eq_nil_or_concat y with hnil | ⟨y0, e, he⟩
              · rw [hnil, hR0]
                refine Finset.sum_eq_zero (fun c _ => ?_)
                have hno : ∀ e : C × Option T, y' ++ [e] ≠ [] := by intro e; simp
                simp only [hno, if_false, Finset.sum_const_zero, ite_self]
              · rw [List.concat_eq_append] at he
                have hy0 : y' = y0 := by rw [hyy, he, List.dropLast_concat]
                obtain ⟨c0, o⟩ := e
                have hiff : ∀ c o', (y' ++ [(c, o')] = y) ↔ (c = c0 ∧ o' = o) := by
                  intro c o'
                  rw [he, hy0]
                  simp
                cases o with
                | none =>
                  have hsub : P.tok c0 ⊆ held y' := by
                    rw [hy0]; exact V1 y0 c0 [] (he ▸ hy)
                  rw [Finset.sum_eq_single c0]
                  · rw [if_pos hsub, if_pos ((hiff c0 none).mpr ⟨rfl, rfl⟩), he, hRn]
                  · intro c _ hc
                    have hno : ∀ o', ¬ (y' ++ [(c, o')] = y) := fun o' h => hc ((hiff c o').mp h).1
                    simp only [hno, if_false, Finset.sum_const_zero, ite_self]
                  · intro h; exact absurd (Finset.mem_univ _) h
                | some t0 =>
                  have hv0 : Valid P (y0 ++ (c0, some t0) :: []) := he ▸ hy
                  have ht1 := V2 _ _ _ _ hv0
                  have ht2 : t0 ∉ held y' := by
                    rw [hy0]; exact fun h => (V3 _ _ _ _ hv0).1 (List.mem_toFinset.mp h)
                  rw [Finset.sum_eq_single c0]
                  · rw [if_neg (fun h => ht2 (h ht1)), Finset.sum_eq_single t0]
                    · rw [if_pos ((hiff c0 (some t0)).mpr ⟨rfl, rfl⟩), he, hRt, hy0]
                    · intro t _ ht
                      exact if_neg (fun h => ht (Option.some.inj ((hiff c0 (some t)).mp h).2))
                    · intro h; exact absurd (Finset.mem_sdiff.mpr ⟨ht1, ht2⟩) h
                  · intro c _ hc
                    have hno : ∀ o', ¬ (y' ++ [(c, o')] = y) := fun o' h => hc ((hiff c o').mp h).1
                    simp only [hno, if_false, Finset.sum_const_zero, ite_self]
                  · intro h; exact absurd (Finset.mem_univ _) h
            · rw [if_neg hyy]
              refine Finset.sum_eq_zero (fun c _ => ?_)
              have hno : ∀ e : C × Option T, ¬ (y' ++ [e] = y) := by
                intro e h; exact hyy (by rw [← h, List.dropLast_concat])
              simp only [hno, if_false, Finset.sum_const_zero, ite_self]
          have hpt : ∀ y', f y' * crate P y' y = (if y' = y.dropLast then R y * f y.dropLast else 0) +
              ∑ p ∈ range (y.length + 1), ∑ c, ∑ t, if y' = ins p c t y then
                P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * f (ins p c t y) else 0 := by
            intro y'
            by_cases hv : Valid P y'
            · have hcr : crate P y' y = (if y' = y.dropLast then R y else 0) +
                  ∑ p ∈ range (y.length + 1), ∑ c, ∑ t, if y' = ins p c t y then
                    P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) else 0 := by
                rw [← hdep y' hv, ← harr y']
                unfold crate ctrans
                rw [List.filter_append, List.map_append, List.sum_append]
                rfl
              rw [hcr, mul_add, Finset.mul_sum]
              congr 1
              · by_cases h : y' = y.dropLast
                · rw [if_pos h, if_pos h, h, mul_comm]
                · rw [if_neg h, if_neg h, mul_zero]
              · refine Finset.sum_congr rfl (fun p _ => ?_)
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun c _ => ?_)
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun t _ => ?_)
                by_cases h : y' = ins p c t y
                · rw [if_pos h, if_pos h, ← h, mul_comm]
                · rw [if_neg h, if_neg h, mul_zero]
            · rw [hfv y' hv, zero_mul]
              symm
              have h1' : (if y' = y.dropLast then R y * f y.dropLast else 0) = 0 := by
                by_cases h : y' = y.dropLast
                · rw [if_pos h, ← h, hfv y' hv, mul_zero]
                · rw [if_neg h]
              rw [h1', zero_add]
              refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun c _ =>
                Finset.sum_eq_zero (fun t _ => ?_)))
              by_cases h : y' = ins p c t y
              · rw [if_pos h, ← h, hfv y' hv, mul_zero]
              · rw [if_neg h]
          rw [hInf, funext hpt]
          exact (hasSum_ite_eq _ _).add (hasSum_sum (fun p _ => hasSum_sum (fun c _ =>
            hasSum_sum (fun t _ => hasSum_ite_eq _ _))))
        have L4c : ∀ y y', 0 ≤ crate P y y' := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          clear hk
          clear h2
          clear h1
          obtain ⟨hl, -, ha, -, -, hs, he⟩ := hS
          intro y y'
          unfold crate
          apply List.sum_nonneg
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨e, he1, rfl⟩ := hx
          have hm := (List.mem_filter.mp he1).1
          unfold ctrans at hm
          rw [List.mem_append] at hm
          rcases hm with hm | hm
          · rw [List.mem_flatMap] at hm
            obtain ⟨c, -, hm⟩ := hm
            split_ifs at hm with h
            · rw [List.mem_singleton] at hm
              subst hm
              exact (hl c).le
            · rw [List.mem_map] at hm
              obtain ⟨t, -, rfl⟩ := hm
              exact mul_nonneg (hl c).le (ha _ _ _)
          · rw [List.mem_flatMap] at hm
            obtain ⟨i, -, hm⟩ := hm
            have hy : 1 ≤ y.length := by have := i.2; omega
            split at hm
            · exact absurd hm List.not_mem_nil
            · rw [List.mem_singleton] at hm
              subst hm
              show 0 ≤ depRate P y i.val
              unfold depRate
              split
              · exact mul_nonneg (he _ hy).le (hs _)
              · exact le_refl _
        have L45M : ∀ (hc0 : ∀ y y', 0 ≤ crate P y y')
          (Q : CState C T → ℝ)
          (hQ : IsStationaryLaw P Q)
          (A : ℕ → Finset (CState C T))
          (hA : ∀ n y, y ∈ A n ↔ y.length = n)
          (hq : ∀ y, HasSum (crate P y) (lamTot P + P.eta y.length * kfun P (heldToks y)))
          (hlev : ∀ n y, ∑ y' ∈ A n, crate P y y' = (if n = y.length + 1 then lamTot P else 0) +
            if n + 1 = y.length then P.eta y.length * kfun P (heldToks y) else 0),
          (∀ n, ∑ y ∈ A n, lamTot P * Q y = ∑ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * Q y) ∧
          (∃ u : ℕ → CState C T → ℝ, (∀ y, u 0 y = 0) ∧
            (∀ n y, u (n + 1) y = if y = [] then Q [] else
              (∑' y', u n y' * crate P y' y) / (lamTot P + P.eta y.length * kfun P (heldToks y))) ∧
            (∀ n y, 0 ≤ u n y) ∧ (∀ n y, u n y ≤ Q y) ∧
            ∀ y, Filter.Tendsto (fun n => u n y) Filter.atTop (nhds (Q y))) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro hc0 Q hQ A hA hq hlev
          have hkn : ∀ l : List T, 0 ≤ kfun P l := by
            intro l
            unfold kfun
            exact Finset.sum_nonneg (fun j _ => hS.2.2.2.2.2.1 _)
          have hk0 : kfun P (heldToks ([] : CState C T)) = 0 := by
            simp [kfun, heldToks]
          have hkp : ∀ y : CState C T, Valid P y → y ≠ [] → 0 < kfun P (heldToks y) := by
            intro y hv hy
            apply hk _ hv.1
            cases y with
            | nil => exact absurd rfl hy
            | cons a l =>
              obtain ⟨c, o⟩ := a
              cases o with
              | some t => intro h; simp [heldToks] at h
              | none =>
                exfalso
                have h := hv.2.2 0 (by simp) rfl
                obtain ⟨t, ht⟩ := hS.2.1 c
                have h2 := h ht
                simp [held, heldToks] at h2
          have hA0 : A 0 = {([] : CState C T)} := by
            ext y
            rw [hA, Finset.mem_singleton, List.length_eq_zero_iff]
          obtain ⟨hQ0, hQ1, hQv, hQr, hQs, hQb⟩ := hQ
          have hlam : 0 ≤ lamTot P := Finset.sum_nonneg (fun c _ => (hS.1 c).le)
          -- sums over a level
          have hH : ∀ (m : ℕ) (g : CState C T → ℝ),
              HasSum (fun y => if y.length = m then g y else 0) (∑ y ∈ A m, g y) := by
            intro m g
            have h1 : HasSum (fun y : CState C T => if y.length = m then g y else 0)
                (∑ y ∈ A m, (if y.length = m then g y else 0)) := by
              apply hasSum_sum_of_ne_finset_zero
              intro y hy
              rw [hA] at hy
              exact if_neg hy
            have h2 : ∑ y ∈ A m, (if y.length = m then g y else 0) = ∑ y ∈ A m, g y := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hA] at hy
              exact if_pos hy
            rw [h2] at h1
            exact h1
          have hsum : ∀ f : CState C T → ℝ, (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Q y) →
              ∀ y, Summable (fun y' => f y' * crate P y' y) := by
            intro f hf0 hfQ y
            refine Summable.of_nonneg_of_le (fun y' => mul_nonneg (hf0 y') (hc0 y' y)) (fun y' => ?_) (hQs y)
            exact mul_le_mul_of_nonneg_right (hfQ y') (hc0 y' y)
          have hswap : ∀ f : CState C T → ℝ, (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Q y) → ∀ n,
              HasSum (fun y' => f y' * ((if n = y'.length + 1 then lamTot P else 0) +
                if n + 1 = y'.length then P.eta y'.length * kfun P (heldToks y') else 0))
                (∑ y ∈ A n, ∑' y', f y' * crate P y' y) := by
            intro f hf0 hfQ n
            have h1 := hasSum_sum (s := A n) (f := fun y y' => f y' * crate P y' y)
              (fun y _ => (hsum f hf0 hfQ y).hasSum)
            refine h1.congr_fun ?_
            intro y'
            rw [← hlev, Finset.mul_sum]
          have hcut0 : ∀ f : CState C T → ℝ, (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Q y) →
              ∑' y', f y' * crate P y' [] = ∑ y ∈ A 1, P.eta 1 * kfun P (heldToks y) * f y := by
            intro f hf0 hfQ
            have h1 := hswap f hf0 hfQ 0
            rw [hA0, Finset.sum_singleton] at h1
            refine h1.unique ((hH 1 (fun y => P.eta 1 * kfun P (heldToks y) * f y)).congr_fun ?_)
            intro y
            by_cases hy : y.length = 1
            · rw [if_neg (by omega), if_pos (by omega), if_pos hy, hy]; ring
            · rw [if_neg (by omega), if_neg (by omega), if_neg hy]; ring
          have hcut : ∀ f : CState C T → ℝ, (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Q y) → ∀ n,
              ∑ y ∈ A (n + 1), ∑' y', f y' * crate P y' y = ∑ y ∈ A n, lamTot P * f y +
                ∑ y ∈ A (n + 2), P.eta (n + 2) * kfun P (heldToks y) * f y := by
            intro f hf0 hfQ n
            refine (hswap f hf0 hfQ (n + 1)).unique (((hH n (fun y => lamTot P * f y)).add
              (hH (n + 2) (fun y => P.eta (n + 2) * kfun P (heldToks y) * f y))).congr_fun ?_)
            intro y
            by_cases hy : y.length = n
            · rw [if_pos (by omega), if_neg (by omega), if_pos hy, if_neg (by omega)]; ring
            · by_cases hy2 : y.length = n + 2
              · rw [if_neg (by omega), if_pos (by omega), if_neg hy, if_pos hy2, hy2]; ring
              · rw [if_neg (by omega), if_neg (by omega), if_neg hy, if_neg hy2]; ring
          have hind : ∀ (f : CState C T → ℝ) (eps : ℝ), (∀ y, 0 ≤ f y) → (∀ y, f y ≤ Q y) →
              (∀ y, y ≠ [] → ∑' y', f y' * crate P y' y =
                f y * (lamTot P + P.eta y.length * kfun P (heldToks y))) →
              (∑' y', f y' * crate P y' [] = f [] * lamTot P - eps) → ∀ n,
              ∑ y ∈ A n, lamTot P * f y =
                ∑ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * f y + eps := by
            intro f eps hf0 hfQ hfb hfe n
            induction n with
            | zero =>
              rw [hA0, Finset.sum_singleton]
              have h1 := hcut0 f hf0 hfQ
              rw [hfe] at h1
              rw [zero_add, ← h1]
              ring
            | succ n ih =>
              have h1 := hcut f hf0 hfQ n
              have h2 : ∑ y ∈ A (n + 1), ∑' y', f y' * crate P y' y =
                  ∑ y ∈ A (n + 1), lamTot P * f y +
                    ∑ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * f y := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro y hy
                rw [hA] at hy
                rw [hfb y (by rintro rfl; simp at hy), hy]
                ring
              have h3 : n + 1 + 1 = n + 2 := rfl
              rw [h3]
              linarith
          have hQb' : ∀ y, ∑' y', Q y' * crate P y' y =
              Q y * (lamTot P + P.eta y.length * kfun P (heldToks y)) := by
            intro y
            have h := hQb y
            rw [(hq y).tsum_eq] at h
            exact h.symm
          constructor
          · skip
            intro n
            have h := hind Q 0 hQ0 (fun y => le_refl _) (fun y _ => hQb' y) (by rw [hQb' [], hk0]; ring) n
            rw [add_zero] at h
            exact_mod_cast h
          · skip
            have hq0 : ∀ y : CState C T, 0 ≤ lamTot P + P.eta y.length * kfun P (heldToks y) := by
              intro y
              exact (hq y).nonneg (hc0 y)
            have hin0 : ∀ f : CState C T → ℝ, (∀ y, 0 ≤ f y) →
                ∀ y, 0 ≤ ∑' y', f y' * crate P y' y := by
              intro f hf0 y
              exact tsum_nonneg (fun y' => mul_nonneg (hf0 y') (hc0 y' y))
            have hinle : ∀ f g : CState C T → ℝ, (∀ y, 0 ≤ f y) → (∀ y, 0 ≤ g y) → (∀ y, f y ≤ g y) →
                (∀ y, g y ≤ Q y) → ∀ y, ∑' y', f y' * crate P y' y ≤ ∑' y', g y' * crate P y' y := by
              intro f g hf0 hg0 hfg hgQ y
              exact Summable.tsum_le_tsum (fun y' => mul_le_mul_of_nonneg_right (hfg y') (hc0 y' y))
                (hsum f hf0 (fun z => (hfg z).trans (hgQ z)) y) (hsum g hg0 hgQ y)
            obtain ⟨u, hu0, hus⟩ : ∃ u : ℕ → CState C T → ℝ, (∀ y, u 0 y = 0) ∧
                (∀ n y, u (n + 1) y = if y = [] then Q [] else
                  (∑' y', u n y' * crate P y' y) / (lamTot P + P.eta y.length * kfun P (heldToks y))) :=
              ⟨fun n => Nat.rec (fun _ => 0) (fun _ v y => if y = [] then Q [] else
                  (∑' y', v y' * crate P y' y) / (lamTot P + P.eta y.length * kfun P (heldToks y))) n,
                fun _ => rfl, fun _ _ => rfl⟩
            have hub : ∀ n, (∀ y, 0 ≤ u n y) ∧ (∀ y, u n y ≤ Q y) := by
              intro n
              induction n with
              | zero => exact ⟨fun y => (hu0 y).ge, fun y => (hu0 y).le.trans (hQ0 y)⟩
              | succ n ih =>
                constructor
                · intro y
                  rw [hus]
                  split_ifs with hy
                  · exact hQ0 []
                  · exact div_nonneg (hin0 _ ih.1 y) (hq0 y)
                · intro y
                  rw [hus]
                  split_ifs with hy
                  · rw [hy]
                  · apply div_le_of_le_mul₀ (hq0 y) (hQ0 y)
                    rw [← hQb' y]
                    exact hinle _ _ ih.1 hQ0 ih.2 (fun _ => le_refl _) y
            have hmono : ∀ n y, u n y ≤ u (n + 1) y := by
              intro n
              induction n with
              | zero =>
                intro y
                rw [hu0]
                exact (hub _).1 y
              | succ n ih =>
                intro y
                rw [hus (n + 1) y, hus n y]
                split_ifs with hy
                · exact le_refl _
                · exact div_le_div_of_nonneg_right
                    (hinle _ _ (hub n).1 (hub (n + 1)).1 ih (hub (n + 1)).2 y) (hq0 y)
            obtain ⟨w, hw⟩ : ∃ w : CState C T → ℝ, ∀ y,
                Filter.Tendsto (fun n => u n y) Filter.atTop (nhds (w y)) :=
              ⟨fun y => ⨆ n, u n y, fun y => tendsto_atTop_ciSup
                (monotone_nat_of_le_succ (fun n => hmono n y))
                ⟨Q y, by rintro _ ⟨n, rfl⟩; exact (hub n).2 y⟩⟩
            have hw0 : ∀ y, 0 ≤ w y := fun y => ge_of_tendsto' (hw y) (fun n => (hub n).1 y)
            have hwQ : ∀ y, w y ≤ Q y := fun y => le_of_tendsto' (hw y) (fun n => (hub n).2 y)
            have hwin : ∀ y, Filter.Tendsto (fun n => ∑' y', u n y' * crate P y' y) Filter.atTop
                (nhds (∑' y', w y' * crate P y' y)) := by
              intro y
              refine tendsto_tsum_of_dominated_convergence (bound := fun y' => Q y' * crate P y' y)
                (hQs y) (fun y' => (hw y').mul_const _) (Filter.Eventually.of_forall (fun n y' => ?_))
              rw [Real.norm_of_nonneg (mul_nonneg ((hub n).1 y') (hc0 y' y))]
              exact mul_le_mul_of_nonneg_right ((hub n).2 y') (hc0 y' y)
            have hwb : ∀ y, y ≠ [] → ∑' y', w y' * crate P y' y =
                w y * (lamTot P + P.eta y.length * kfun P (heldToks y)) := by
              intro y hy
              have h1 : ∀ n, u (n + 1) y * (lamTot P + P.eta y.length * kfun P (heldToks y)) =
                  ∑' y', u n y' * crate P y' y := by
                intro n
                rw [hus, if_neg hy]
                by_cases hz : lamTot P + P.eta y.length * kfun P (heldToks y) = 0
                · have h2 := hinle _ _ (hub n).1 hQ0 (hub n).2 (fun _ => le_refl _) y
                  rw [hQb' y, hz, mul_zero] at h2
                  rw [hz, mul_zero]
                  exact le_antisymm (hin0 _ (hub n).1 y) h2
                · exact div_mul_cancel₀ _ hz
              have h2 := (((Filter.tendsto_add_atTop_iff_nat 1).2 (hw y)).mul_const
                (lamTot P + P.eta y.length * kfun P (heldToks y)))
              refine tendsto_nhds_unique (hwin y) (h2.congr h1)
            have hwe : w [] = Q [] := by
              refine tendsto_nhds_unique ((Filter.tendsto_add_atTop_iff_nat 1).2 (hw [])) ?_
              refine tendsto_const_nhds.congr (fun n => ?_)
              rw [hus, if_pos rfl]
            have hQe : ∑' y', Q y' * crate P y' [] = Q [] * lamTot P := by
              rw [hQb' [], hk0]; ring
            obtain ⟨eps, heps⟩ : ∃ eps : ℝ, eps = Q [] * lamTot P - ∑' y', w y' * crate P y' [] := ⟨_, rfl⟩
            have heps0 : 0 ≤ eps := by
              have h := hinle _ _ hw0 hQ0 hwQ (fun _ => le_refl _) []
              rw [hQe] at h
              linarith
            have hwcut := hind w eps hw0 hwQ hwb (by rw [hwe, heps]; ring)
            have hQcut := hind Q 0 hQ0 (fun y => le_refl _) (fun y _ => hQb' y) (by rw [hQe]; ring)
            have hfl0 : ∀ n, 0 ≤ ∑ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * w y := by
              intro n
              exact Finset.sum_nonneg (fun y _ => mul_nonneg
                (mul_nonneg (hS.2.2.2.2.2.2 _ (by omega)).le (hkn _)) (hw0 y))
            have hQn : Summable (fun n => ∑ y ∈ A n, Q y) := by
              refine summable_of_sum_range_le (c := 1) (fun n => Finset.sum_nonneg (fun y _ => hQ0 y)) ?_
              intro N
              rw [← Finset.sum_biUnion]
              · exact sum_le_hasSum _ (fun y _ => hQ0 y) hQ1
              · intro i _ j _ hij
                refine Finset.disjoint_left.2 (fun y h1 h2 => hij ?_)
                rw [hA] at h1 h2
                exact h1.symm.trans h2
            have heps1 : eps ≤ 0 := by
              have h := hQn.tendsto_atTop_zero.const_mul (lamTot P)
              rw [mul_zero] at h
              refine ge_of_tendsto' h (fun n => ?_)
              have h1 := hwcut n
              have h2 := hfl0 n
              have h3 : ∑ y ∈ A n, lamTot P * w y ≤ ∑ y ∈ A n, lamTot P * Q y :=
                Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hwQ y) hlam)
              rw [Finset.mul_sum]
              linarith
            have heps2 : eps = 0 := le_antisymm heps1 heps0
            have hall : ∀ n, ∀ y ∈ A n, w y = Q y := by
              intro n
              induction n with
              | zero =>
                intro y hy
                rw [hA0, Finset.mem_singleton] at hy
                rw [hy, hwe]
              | succ n ih =>
                have h1 := hwcut n
                have h2 := hQcut n
                have h3 : ∑ y ∈ A n, lamTot P * w y = ∑ y ∈ A n, lamTot P * Q y :=
                  Finset.sum_congr rfl (fun y hy => by rw [ih y hy])
                have h4 : ∑ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * (Q y - w y) = 0 := by
                  have h5 : ∀ y ∈ A (n + 1), P.eta (n + 1) * kfun P (heldToks y) * (Q y - w y) =
                      P.eta (n + 1) * kfun P (heldToks y) * Q y -
                        P.eta (n + 1) * kfun P (heldToks y) * w y := fun y _ => by ring
                  rw [Finset.sum_congr rfl h5, Finset.sum_sub_distrib]
                  linarith
                have heta : 0 < P.eta (n + 1) := hS.2.2.2.2.2.2 _ (by omega)
                have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => mul_nonneg
                  (mul_nonneg heta.le (hkn (heldToks y))) (sub_nonneg.2 (hwQ y)))).1 h4
                intro y hy
                by_cases hv : Valid P y
                · have hy2 : y ≠ [] := by
                    rintro rfl
                    rw [hA] at hy
                    simp at hy
                  rcases mul_eq_zero.1 (h6 y hy) with h7 | h7
                  · exact absurd h7 (mul_pos heta (hkp y hv hy2)).ne'
                  · linarith
                · have h7 := hQv y hv
                  have h8 := hw0 y
                  have h9 := hwQ y
                  linarith
            refine ⟨u, hu0, hus, fun n => (hub n).1, fun n => (hub n).2, fun y => ?_⟩
            rw [← hall y.length y ((hA _ _).2 rfl)]
            exact hw y
        have L6 : ∀ (ins : ℕ → C → T → CState C T → CState C T)
          (hins : ∀ p c t y, ins p c t y = y.take p ++ (c, some t) ::
            (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e))
          (R : CState C T → ℝ)
          (hR0 : R [] = 0)
          (hRn : ∀ y c, R (y ++ [(c, none)]) = P.lam c)
          (hRt : ∀ y c t, R (y ++ [(c, some t)]) = P.lam c * P.assign c (held y) t)
          (Inf : (CState C T → ℝ) → CState C T → ℝ)
          (hInf : ∀ f y, Inf f y = R y * f y.dropLast + ∑ p ∈ range (y.length + 1), ∑ c, ∑ t,
            P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * f (ins p c t y))
          (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (sk : CState C T → List (Option (C × Option T)))
          (hsk : ∀ y, sk y = y.map (fun e => if e.2 = none then none else some e))
          (f : CState C T → ℝ)
          (hfv : ∀ y, ¬ Valid P y → f y = 0)
          (ih : ∀ y y', Valid P y → Valid P y' → sk y = sk y' → f y * lamIn y' = f y' * lamIn y),
          ∀ y y', Valid P y → Valid P y' → sk y = sk y' → Inf f y * lamIn y' = Inf f y' * lamIn y := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro ins hins R hR0 hRn hRt Inf hInf lamIn hlamIn sk hsk f hfv ih
          classical
          have hlam : ∀ c, 0 < P.lam c := hS.1
          -- facts on `sk`
          have skapp : ∀ a b, sk (a ++ b) = sk a ++ sk b := by
            intro a b; rw [hsk, hsk, hsk, List.map_append]
          have sktake : ∀ n a, sk (a.take n) = (sk a).take n := by
            intro n a; rw [hsk, hsk, List.map_take]
          have skdrop : ∀ n a, sk (a.drop n) = (sk a).drop n := by
            intro n a; rw [hsk, hsk, List.map_drop]
          have sklen : ∀ a, (sk a).length = a.length := by
            intro a; rw [hsk, List.length_map]
          have skheld : ∀ a, heldToks a = (sk a).filterMap (fun o => o.bind Prod.snd) := by
            intro a
            rw [hsk, List.filterMap_map]
            unfold heldToks
            congr 1
            funext e
            rcases e with ⟨c, _ | t⟩ <;> rfl
          have skheld' : ∀ a b, sk a = sk b → heldToks a = heldToks b := by
            intro a b h; rw [skheld, skheld, h]
          have skg : ∀ t a, sk (a.map (fun e : C × Option T => if e.2 = some t then (e.1, none) else e))
              = (sk a).map (fun o => o.bind (fun e => if e.2 = some t then none else some e)) := by
            intro t a
            rw [hsk, hsk, List.map_map, List.map_map]
            congr 1
            funext e
            rcases e with ⟨c, _ | u⟩
            · rfl
            · by_cases h : u = t
              · subst h; simp
              · simp [h]
          have skins : ∀ p c t y y', sk y = sk y' → sk (ins p c t y) = sk (ins p c t y') := by
            intro p c t y y' h
            have e1 : ∀ z, sk (ins p c t z) = (sk z).take p ++ (some (c, some t) :: ((sk z).drop p).map
                (fun o => o.bind (fun e => if e.2 = some t then none else some e))) := by
              intro z
              rw [hins, skapp, sktake, ← skdrop, ← skg]
              congr 1
              rw [hsk, hsk, List.map_cons]
              rfl
            rw [e1, e1, h]
          -- entries
          have skent : ∀ a b : CState C T, sk a = sk b → ∀ (i : ℕ) (e' : C × Option T), b[i]? = some e' →
              ∃ e, a[i]? = some e ∧ (e.2 = none ↔ e'.2 = none) ∧ (e'.2 ≠ none → e = e') := by
            intro a b h i e' he'
            have h1 : (sk a)[i]? = (sk b)[i]? := by rw [h]
            rw [hsk, hsk, List.getElem?_map, List.getElem?_map, he'] at h1
            rcases hae : a[i]? with _ | e
            · rw [hae] at h1; simp at h1
            · refine ⟨e, rfl, ?_⟩
              rw [hae] at h1
              rcases e with ⟨x, _ | u⟩ <;> rcases e' with ⟨x', _ | u'⟩ <;> simp at h1 ⊢
              exact h1
          have hgA : ∀ (A B : CState C T) (j : ℕ), (A ++ B)[A.length + j]? = B[j]? := by
            intro A B j
            rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          -- validity by entries
          have hVal : ∀ y : CState C T, Valid P y ↔ (heldToks y).Nodup ∧
              ∀ (i : ℕ) (e : C × Option T), y[i]? = some e →
                (∀ t, e.2 = some t → t ∈ P.tok e.1) ∧ (e.2 = none → P.tok e.1 ⊆ held (y.take i)) := by
            intro y
            constructor
            · rintro ⟨h1, h2, h3⟩
              refine ⟨h1, ?_⟩
              intro i e he
              obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 he
              exact ⟨h2 i hi, h3 i hi⟩
            · rintro ⟨h1, h2⟩
              refine ⟨h1, ?_, ?_⟩
              · intro i hi
                exact (h2 i _ (List.getElem?_eq_getElem hi)).1
              · intro i hi
                exact (h2 i _ (List.getElem?_eq_getElem hi)).2
          have hValDL : ∀ (y : CState C T) e, Valid P (y ++ [e]) → Valid P y := by
            intro y e h
            rw [hVal] at h ⊢
            refine ⟨?_, ?_⟩
            · have := h.1
              unfold heldToks at this ⊢
              rw [List.filterMap_append] at this
              exact this.of_append_left
            · intro i a ha
              have hi : i < y.length := (List.getElem?_eq_some_iff.1 ha).1
              have h2 := h.2 i a (by rw [List.getElem?_append_left hi]; exact ha)
              rw [List.take_append_of_le_length hi.le] at h2
              exact h2
          -- transfer of validity
          have hVT : ∀ p c t y y', sk y = sk y' → Valid P y' → Valid P (ins p c t y) →
              Valid P (ins p c t y') := by
            intro p c t y y' h hy' hz
            have hskz : sk (ins p c t y) = sk (ins p c t y') := skins p c t y y' h
            rw [hVal] at hz ⊢
            have hy'2 := ((hVal y').1 hy').2
            refine ⟨by rw [← skheld' _ _ hskz]; exact hz.1, ?_⟩
            intro i e' he'
            obtain ⟨e, he, hn, hs⟩ := skent _ _ hskz i e' he'
            have hheld : held ((ins p c t y).take i) = held ((ins p c t y').take i) := by
              unfold held
              rw [skheld' _ _ (show sk ((ins p c t y).take i) = sk ((ins p c t y').take i) by
                rw [sktake, sktake, hskz])]
            have hzi := hz.2 i e he
            refine ⟨?_, ?_⟩
            · intro u hu
              have : e = e' := hs (by rw [hu]; simp)
              rw [← this] at hu ⊢
              exact hzi.1 u hu
            · intro hnone
              have key : ∀ j (x : C × Option T), y'[j]? = some x → x.2 = none →
                  held (y'.take j) ⊆ held ((ins p c t y').take i) → P.tok x.1 ⊆ held ((ins p c t y').take i) :=
                fun j x hx hx2 hsub => ((hy'2 j x hx).2 hx2).trans hsub
              by_cases hip : i < (y'.take p).length
              · have hip2 : i < p := by
                  rw [List.length_take] at hip; omega
                have e1 : y'[i]? = some e' := by
                  have e2 := he'
                  rw [hins, List.getElem?_append_left hip, List.getElem?_take_of_lt hip2] at e2
                  exact e2
                refine key i e' e1 hnone ?_
                rw [hins, List.take_append_of_le_length hip.le, List.take_take, min_eq_left hip2.le]
              · by_cases hip3 : i = (y'.take p).length
                · exfalso
                  have e2 := he'
                  rw [hins, hip3, List.getElem?_append_right le_rfl, Nat.sub_self] at e2
                  simp at e2
                  rw [← e2] at hnone
                  simp at hnone
                · obtain ⟨j, hj⟩ : ∃ j, i = (y'.take p).length + (j + 1) :=
                    ⟨i - (y'.take p).length - 1, by omega⟩
                  have e2 := he'
                  rw [hins, hj, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
                    List.getElem?_cons_succ, List.getElem?_map] at e2
                  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.1 e2
                  have hx' : y'[(y'.take p).length + j]? = some x := by
                    have e6 := hgA (y'.take p) (y'.drop p) j
                    rw [List.take_append_drop] at e6
                    rw [e6]; exact hx
                  by_cases hxt : x.2 = some t
                  · -- active in `y'`, hence the same in `y`
                    obtain ⟨x0, hx0, -, hxs⟩ := skent _ _ h _ x hx'
                    have hx0x : x0 = x := hxs (by rw [hxt]; simp)
                    have hlen : y.length = y'.length := by rw [← sklen y, ← sklen y', h]
                    have hlt : (y.take p).length = (y'.take p).length := by
                      rw [List.length_take, List.length_take, hlen]
                    have hee : e = e' := by
                      have e3 := he
                      rw [hins, hj, ← hlt, List.getElem?_append_right (Nat.le_add_right _ _),
                        Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_map] at e3
                      have hx0' : (y.drop p)[j]? = some x := by
                        have e6 := hgA (y.take p) (y.drop p) j
                        rw [List.take_append_drop, hlt, hx0] at e6
                        rw [← e6, hx0x]
                      rw [hx0'] at e3
                      rw [← hxe]
                      exact (Option.some.inj e3).symm
                    rw [← hee, ← hheld]
                    exact hzi.2 (by rw [hee]; exact hnone)
                  · have hxe' : x = e' := by rw [← hxe, if_neg hxt]
                    rw [← hxe']
                    refine key _ x hx' (by rw [hxe']; exact hnone) ?_
                    intro u hu
                    rw [hins, hj]
                    have e4 : (y'.take p ++ (c, some t) :: (y'.drop p).map
                        (fun e => if e.2 = some t then (e.1, none) else e)).take ((y'.take p).length + (j + 1))
                        = y'.take p ++ (c, some t) :: ((y'.drop p).take j).map
                        (fun e => if e.2 = some t then (e.1, none) else e) := by
                      rw [List.take_length_add_append, List.take_succ_cons, List.map_take]
                    rw [e4]
                    have e5 : y'.take ((y'.take p).length + j) = y'.take p ++ (y'.drop p).take j := by
                      have e6 := List.take_length_add_append (l₁ := y'.take p) (l₂ := y'.drop p) j
                      rw [List.take_append_drop] at e6
                      exact e6
                    rw [e5] at hu
                    unfold held heldToks at hu ⊢
                    rw [List.mem_toFinset, List.mem_filterMap] at hu ⊢
                    obtain ⟨w, hw, hwu⟩ := hu
                    by_cases hut : u = t
                    · exact ⟨(c, some t), by simp, by rw [hut]⟩
                    · refine ⟨w, ?_, hwu⟩
                      rw [List.mem_append] at hw ⊢
                      rcases hw with hw | hw
                      · exact Or.inl hw
                      · refine Or.inr (List.mem_cons_of_mem _ (List.mem_map.2 ⟨w, hw, ?_⟩))
                        rw [if_neg]
                        rw [hwu]
                        intro hh
                        exact hut (Option.some.inj hh)
          -- lamIn
          have lamapp : ∀ a b, lamIn (a ++ b) = lamIn a * lamIn b := by
            intro a b; rw [hlamIn, hlamIn, hlamIn, List.map_append, List.prod_append]
          have hrho : ∀ p c t y y', sk y = sk y' → ∃ ρ : ℝ, 0 < ρ ∧
              lamIn (ins p c t y) = lamIn y * ρ ∧ lamIn (ins p c t y') = lamIn y' * ρ := by
            intro p c t y y' h
            have hl : ∀ l : CState C T,
                lamIn (l.map (fun e => if e.2 = some t then (e.1, none) else e)) = lamIn l *
                ((sk l).map (fun o => o.elim 1 (fun e => if e.2 = some t then P.lam e.1 else 1))).prod := by
              intro l
              rw [hlamIn, hlamIn, hsk, List.map_map, List.map_map, ← List.prod_map_mul]
              congr 1
              refine List.map_congr_left ?_
              rintro ⟨x, _ | u⟩ -
              · simp
              · by_cases hu : u = t
                · subst hu; simp
                · simp [hu]
            have hz : ∀ z, lamIn (ins p c t z) = lamIn z *
                (((sk z).drop p).map (fun o => o.elim 1 (fun e => if e.2 = some t then P.lam e.1 else 1))).prod := by
              intro z
              rw [hins, lamapp, ← List.singleton_append, lamapp, hl, skdrop]
              have e1 : lamIn [(c, some t)] = 1 := by rw [hlamIn]; simp
              have e2 : lamIn z = lamIn (z.take p) * lamIn (z.drop p) := by
                rw [← lamapp, List.take_append_drop]
              rw [e1, e2]
              ring
            refine ⟨(((sk y).drop p).map
              (fun o => o.elim 1 (fun e => if e.2 = some t then P.lam e.1 else 1))).prod, ?_, hz y, ?_⟩
            · refine List.prod_pos ?_
              intro a ha
              obtain ⟨o, -, rfl⟩ := List.mem_map.1 ha
              rcases o with _ | e
              · exact one_pos
              · show 0 < (if e.2 = some t then P.lam e.1 else 1)
                split_ifs
                · exact hlam _
                · exact one_pos
            · rw [h]; exact hz y'
          -- the main computation
          intro y y' hy hy' h
          have hlen : y.length = y'.length := by rw [← sklen y, ← sklen y', h]
          have harr : R y * f y.dropLast * lamIn y' = R y' * f y'.dropLast * lamIn y := by
            rcases List.eq_nil_or_concat y with h0 | ⟨a, e, hae⟩
            · have h0' : y' = [] := List.length_eq_zero_iff.1 (by rw [← hlen, h0]; rfl)
              rw [h0, h0']
            · rcases List.eq_nil_or_concat y' with h0' | ⟨a', e', hae'⟩
              · exfalso
                rw [h0', hae] at hlen
                simp at hlen
              · rw [List.concat_eq_append] at hae hae'
                have h2 := h
                rw [hae, hae', skapp, skapp] at h2
                obtain ⟨hsa, hse⟩ := List.append_inj' h2 (by rw [sklen, sklen]; rfl)
                have hia := ih a a' (hValDL a e (by rw [← hae]; exact hy))
                  (hValDL a' e' (by rw [← hae']; exact hy')) hsa
                have hheld : held a = held a' := by unfold held; rw [skheld' _ _ hsa]
                rw [hae, hae', List.dropLast_concat, List.dropLast_concat, lamapp, lamapp]
                rcases e with ⟨x, _ | u⟩ <;> rcases e' with ⟨x', _ | u'⟩
                · have l1 : lamIn [(x, none)] = P.lam x := by rw [hlamIn]; simp
                  have l2 : lamIn [(x', none)] = P.lam x' := by rw [hlamIn]; simp
                  rw [hRn, hRn, l1, l2]
                  linear_combination (P.lam x * P.lam x') * hia
                · exfalso; rw [hsk, hsk] at hse; simp at hse
                · exfalso; rw [hsk, hsk] at hse; simp at hse
                · rw [hsk, hsk] at hse
                  simp at hse
                  obtain ⟨rfl, rfl⟩ := hse
                  have l1 : lamIn [(x, some u)] = 1 := by rw [hlamIn]; simp
                  rw [hRt, hRt, l1, hheld]
                  linear_combination (P.lam x * P.assign x (held a') u) * hia
          have hdep : ∀ p c t, f (ins p c t y) * lamIn y' = f (ins p c t y') * lamIn y := by
            intro p c t
            by_cases hv : Valid P (ins p c t y)
            · have hv' := hVT p c t y y' h hy' hv
              obtain ⟨ρ, hρ, e1, e2⟩ := hrho p c t y y' h
              have hi := ih _ _ hv hv' (skins p c t y y' h)
              rw [e1, e2] at hi
              refine mul_right_cancel₀ hρ.ne' ?_
              linear_combination hi
            · have hv' : ¬ Valid P (ins p c t y') := fun hv' => hv (hVT p c t y' y h.symm hy hv')
              rw [hfv _ hv, hfv _ hv', zero_mul, zero_mul]
          rw [hInf, hInf, add_mul, add_mul, harr, hlen]
          congr 1
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [skheld' (y.take p) (y'.take p) (by rw [sktake, sktake, h])]
          linear_combination (P.eta (y'.length + 1) * P.s (heldToks (y'.take p) ++ [t])) * hdep p c t
        have L7M : ∀ (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (Pi : CState C T → ℝ)
          (hPi : ∀ y, Pi y = piLam P (heldToks y) * lamIn y *
            (∏ q ∈ range y.length, (kfun P (heldToks (y.take (q + 1))))⁻¹) *
            ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹)
          (t : T),
          (∀ (ins : ℕ → C → T → CState C T → CState C T) (hins : ∀ p c t y, ins p c t y = y.take p ++ (c, some t) ::
            (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e)) (y : CState C T) (hy : Valid P y) (c : C) (ht : t ∉ held y), ∑ p ∈ range (y.length + 1), P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * Pi (ins p c t y)
            = lamTok P (held y) t * Pi y) ∧
          (∀ (a b : CState C T) (g : C) (hy : Valid P (a ++ (g, some t) :: b)) (c g' : C), ∑ p ∈ range (a.length + 1), P.eta ((a ++ (g, some t) :: b).length + 1) * P.s (heldToks (a.take p) ++ [t]) *
            Pi (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b))
            = P.lam g' * Pi (a ++ (g, some t) :: b)) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro lamIn hlamIn Pi hPi t
          have hhap : ∀ u v : CState C T, heldToks (u ++ v) = heldToks u ++ heldToks v := by
            intro u v; exact List.filterMap_append
          have hhcs : ∀ (x : C) (z : T) (v : CState C T), heldToks ((x, some z) :: v) = z :: heldToks v := by
            intro x z v; rfl
          have hhcn : ∀ (x : C) (v : CState C T), heldToks ((x, none) :: v) = heldToks v := by
            intro x v; rfl
          have hhnil : heldToks ([] : CState C T) = [] := rfl
          have hKs : ∀ (l : List T) (z : T), kfun P (l ++ [z]) = kfun P l + P.s (l ++ [z]) := by
            intro l z
            unfold kfun
            rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              rw [List.take_append_of_le_length (by have := Finset.mem_range.1 hj; omega)]
            · rw [List.take_of_length_le (by rw [List.length_append, List.length_singleton])]
          have hK0 : kfun P ([] : List T) = 0 := by unfold kfun; rfl
          obtain ⟨W, hW⟩ : ∃ W : List T → CState C T → ℝ, ∀ l u, W l u =
              ∏ q ∈ range u.length, (kfun P (l ++ heldToks (u.take (q + 1))))⁻¹ := ⟨_, fun _ _ => rfl⟩
          have hWnil : ∀ l, W l [] = 1 := by
            intro l; rw [hW]; rfl
          have hWcons : ∀ l e u, W l (e :: u) =
              (kfun P (l ++ heldToks [e]))⁻¹ * W (l ++ heldToks [e]) u := by
            intro l e u
            rw [hW, hW, List.length_cons, Finset.prod_range_succ', mul_comm]
            congr 1
            apply Finset.prod_congr rfl
            intro q hq
            rw [List.take_succ_cons, ← List.singleton_append, hhap, List.append_assoc]
          have hWap : ∀ (u v : CState C T) (l : List T), W l (u ++ v) = W l u * W (l ++ heldToks u) v := by
            intro u v
            induction u with
            | nil => intro l; rw [hWnil, hhnil, List.append_nil, one_mul, List.nil_append]
            | cons e u ih =>
              intro l
              rw [List.cons_append, hWcons, hWcons, ih, mul_assoc]
              congr 3
              rw [List.append_assoc, ← hhap]; rfl
          have hWperm : ∀ (u : CState C T) (l l' : List T), (l ++ heldToks u).Nodup → l.Perm l' →
              W l u = W l' u := by
            intro u
            induction u with
            | nil => intro l l' _ _; rw [hWnil, hWnil]
            | cons e u ih =>
              intro l l' hn hp
              have e1 : l ++ heldToks (e :: u) = (l ++ heldToks [e]) ++ heldToks u := by
                rw [List.append_assoc, ← hhap]; rfl
              rw [e1] at hn
              rw [hWcons, hWcons, ih _ _ hn (hp.append_right _),
                h2 _ _ (List.Nodup.of_append_left hn) (hp.append_right _)]
          have hG : ∀ (a : CState C T) (t : T), (heldToks a ++ [t]).Nodup →
              (∀ e u, a = e :: u → e.2 ≠ none) →
              ∑ p ∈ range (a.length + 1), P.s (heldToks (a.take p) ++ [t]) * (W [] (a.take p) *
                ((kfun P (heldToks (a.take p) ++ [t]))⁻¹ *
                  W (heldToks (a.take p) ++ [t]) (a.drop p))) = W [] a := by
            intro a t
            induction a using List.reverseRecOn with
            | nil =>
              intro hn _
              have hpos := hk [t] (List.nodup_singleton t) (List.cons_ne_nil _ _)
              have e1 : kfun P [t] = P.s [t] := by
                have := hKs [] t
                rw [List.nil_append, hK0, zero_add] at this
                exact this
              rw [List.length_nil, zero_add, Finset.sum_range_one, List.take_nil, List.drop_nil, hhnil,
                List.nil_append, hWnil, hWnil, mul_one, one_mul, ← e1]
              exact mul_inv_cancel₀ (ne_of_gt hpos)
            | append_singleton a e ih =>
              intro hn hh
              have hn1 : (heldToks (a ++ [e])).Nodup := List.Nodup.of_append_left hn
              have hsub : (heldToks a ++ [t]).Sublist (heldToks (a ++ [e]) ++ [t]) := by
                rw [hhap]
                exact (List.sublist_append_left _ _).append_right _
              have ih' := ih (hn.sublist hsub) (by
                intro e' u hu
                exact hh e' (u ++ [e]) (by rw [hu]; rfl))
              have hne : heldToks (a ++ [e]) ≠ [] := by
                cases a with
                | nil =>
                  have := hh e [] rfl
                  obtain ⟨x, o⟩ := e
                  cases o with
                  | none => exact absurd rfl this
                  | some z => intro h0; rw [List.nil_append, hhcs] at h0; exact List.cons_ne_nil _ _ h0
                | cons e' u =>
                  have := hh e' (u ++ [e]) rfl
                  obtain ⟨x, o⟩ := e'
                  cases o with
                  | none => exact absurd rfl this
                  | some z => intro h0; rw [List.cons_append, hhcs] at h0; exact List.cons_ne_nil _ _ h0
              have hK1 : kfun P (heldToks (a ++ [e])) ≠ 0 := ne_of_gt (hk _ hn1 hne)
              have hK2 : kfun P (heldToks (a ++ [e]) ++ [t]) ≠ 0 :=
                ne_of_gt (hk _ hn (by intro h0; exact absurd (List.append_eq_nil_iff.1 h0).2 (List.cons_ne_nil _ _)))
              have hWa : W [] (a ++ [e]) = W [] a * (kfun P (heldToks (a ++ [e])))⁻¹ := by
                rw [hWap, hWcons, hWnil, mul_one, List.nil_append, ← hhap]
              have hstep : ∀ p ∈ range (a.length + 1),
                  P.s (heldToks ((a ++ [e]).take p) ++ [t]) * (W [] ((a ++ [e]).take p) *
                ((kfun P (heldToks ((a ++ [e]).take p) ++ [t]))⁻¹ *
                  W (heldToks ((a ++ [e]).take p) ++ [t]) ((a ++ [e]).drop p))) =
                  P.s (heldToks (a.take p) ++ [t]) * (W [] (a.take p) *
                ((kfun P (heldToks (a.take p) ++ [t]))⁻¹ *
                  W (heldToks (a.take p) ++ [t]) (a.drop p))) *
                    (kfun P (heldToks (a ++ [e]) ++ [t]))⁻¹ := by
                intro p hp
                have hp' : p ≤ a.length := by have := Finset.mem_range.1 hp; omega
                have hperm : (heldToks (a ++ [e]) ++ [t]).Perm
                    (heldToks (a.take p) ++ [t] ++ heldToks (a.drop p) ++ heldToks [e]) := by
                  rw [hhap]
                  nth_rewrite 1 [← List.take_append_drop p a]
                  rw [hhap]
                  apply List.perm_iff_count.2
                  intro z
                  simp only [List.count_append]
                  omega
                rw [List.take_append_of_le_length hp', List.drop_append_of_le_length hp', hWap,
                  hWcons, hWnil, mul_one, h2 _ _ hn hperm]
                ring
              rw [List.length_append, List.length_singleton, Finset.sum_range_succ,
                Finset.sum_congr rfl hstep, ← Finset.sum_mul, ih',
                List.take_of_length_le (by rw [List.length_append, List.length_singleton]),
                List.drop_eq_nil_of_le (by rw [List.length_append, List.length_singleton]), hWnil, mul_one]
              have hKt := hKs (heldToks (a ++ [e])) t
              have hWb : W [] a = W [] (a ++ [e]) * kfun P (heldToks (a ++ [e])) := by
                rw [hWa, mul_assoc, inv_mul_cancel₀ hK1, mul_one]
              rw [hWb]
              have : W [] (a ++ [e]) * kfun P (heldToks (a ++ [e])) *
                  (kfun P (heldToks (a ++ [e]) ++ [t]))⁻¹ + P.s (heldToks (a ++ [e]) ++ [t]) *
                  (W [] (a ++ [e]) * (kfun P (heldToks (a ++ [e]) ++ [t]))⁻¹) =
                  W [] (a ++ [e]) * ((kfun P (heldToks (a ++ [e])) + P.s (heldToks (a ++ [e]) ++ [t])) *
                    (kfun P (heldToks (a ++ [e]) ++ [t]))⁻¹) := by ring
              rw [this, ← hKt, mul_inv_cancel₀ hK2, mul_one]
          have hG2 : ∀ (a r : CState C T) (t : T) (c : C), (heldToks a ++ [t] ++ heldToks r).Nodup →
              (∀ e u, a = e :: u → e.2 ≠ none) →
              ∑ p ∈ range (a.length + 1), P.s (heldToks (a.take p) ++ [t]) *
                W [] (a.take p ++ (c, some t) :: (a.drop p ++ r)) = W [] a * W (heldToks a ++ [t]) r := by
            intro a r t c hn hh
            rw [← hG a t (List.Nodup.of_append_left hn) hh, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro p hp
            have hperm : (heldToks a ++ [t]).Perm
                (heldToks (a.take p) ++ [t] ++ heldToks (a.drop p)) := by
              nth_rewrite 1 [← List.take_append_drop p a]
              rw [hhap]
              apply List.perm_iff_count.2
              intro z
              simp only [List.count_append]
              omega
            have hcs : heldToks [(c, some t)] = [t] := rfl
            rw [hWap, List.nil_append, hWcons, hcs, hWap, hWperm r _ _ hn hperm]
            ring
          have hPi' : ∀ u : CState C T, Pi u = piLam P (heldToks u) * lamIn u * W [] u *
              ∏ q ∈ range u.length, (P.eta (q + 1))⁻¹ := by
            intro u
            rw [hPi, hW]
            rfl
          have hhead : ∀ u : CState C T, Valid P u → ∀ e v, u = e :: v → e.2 ≠ none := by
            intro u hu e v hev h0
            subst hev
            have h3 := hu.2.2 0 (Nat.succ_pos _) h0
            obtain ⟨z, hz⟩ := hS.2.1 e.1
            have h4 := h3 hz
            rw [List.take_zero] at h4
            exact absurd h4 (by unfold held; rw [hhnil]; exact List.not_mem_nil ∘ List.mem_toFinset.1)
          have hlamap : ∀ u v : CState C T, lamIn (u ++ v) = lamIn u * lamIn v := by
            intro u v
            rw [hlamIn, hlamIn, hlamIn, List.map_append, List.prod_append]
          have hlams : ∀ (x : C) (z : T) (v : CState C T), lamIn ((x, some z) :: v) = lamIn v := by
            intro x z v
            rw [hlamIn, hlamIn, List.map_cons, List.prod_cons, if_neg (Option.some_ne_none z), one_mul]
          have hlamn : ∀ (x : C) (v : CState C T), lamIn ((x, none) :: v) = P.lam x * lamIn v := by
            intro x v
            rw [hlamIn, hlamIn, List.map_cons, List.prod_cons, if_pos rfl]
          have hetac : ∀ n : ℕ, P.eta (n + 1) * ∏ q ∈ range (n + 1), (P.eta (q + 1))⁻¹ =
              ∏ q ∈ range n, (P.eta (q + 1))⁻¹ := by
            intro n
            have h0 : P.eta (n + 1) ≠ 0 := ne_of_gt (hS.2.2.2.2.2.2 (n + 1) (Nat.succ_pos n))
            rw [Finset.prod_range_succ, mul_comm, mul_assoc, inv_mul_cancel₀ h0, mul_one]
          constructor
          · intro ins hins y hy c ht
            have hmap : ∀ p, (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e) = y.drop p := by
              intro p
              refine Eq.trans (List.map_congr_left ?_) (List.map_id' (y.drop p))
              intro e he
              apply if_neg
              intro h0
              apply ht
              unfold held
              rw [List.mem_toFinset]
              unfold heldToks
              exact List.mem_filterMap.2 ⟨e, List.mem_of_mem_drop he, h0⟩
            have hn : (heldToks y ++ [t]).Nodup := by
              have ht' : t ∉ heldToks y := fun h => ht (List.mem_toFinset.2 h)
              exact hy.1.append (List.nodup_singleton t) (by
                intro z hz hz'
                rw [List.mem_singleton] at hz'
                exact ht' (hz' ▸ hz))
            have hpl : piLam P (heldToks y ++ [t]) = piLam P (heldToks y) * lamTok P (held y) t := by
              have hr : ∀ (l : List T) (n : ℕ), n = l.length → piLam P l = ∏ j ∈ range n,
                  (if h : j < l.length then lamTok P (l.take j).toFinset (l[j]'h) else 1) := by
                intro l n hnl
                subst hnl
                rw [Finset.prod_range]
                unfold piLam
                apply Finset.prod_congr rfl
                intro j _
                rw [dif_pos j.2]
                rfl
              rw [hr (heldToks y ++ [t]) ((heldToks y).length + 1) (by rw [List.length_append, List.length_singleton]),
                hr (heldToks y) _ rfl, Finset.prod_range_succ]
              congr 1
              · apply Finset.prod_congr rfl
                intro j hj
                have hj' := Finset.mem_range.1 hj
                rw [dif_pos hj', dif_pos (by rw [List.length_append, List.length_singleton]; omega),
                  List.take_append_of_le_length (le_of_lt hj'), List.getElem_append_left hj']
              · rw [dif_pos (by rw [List.length_append, List.length_singleton]; omega),
                  List.take_append_of_le_length (le_refl _), List.take_length, List.getElem_concat_length rfl]
                rfl
            have hterm : ∀ p ∈ range (y.length + 1),
                P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * Pi (ins p c t y) =
                (piLam P (heldToks y) * lamTok P (held y) t * lamIn y *
                  ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹) * (P.s (heldToks (y.take p) ++ [t]) *
                  W [] (y.take p ++ (c, some t) :: (y.drop p ++ []))) := by
              intro p hp
              have hperm : (heldToks y ++ [t]).Perm
                  (heldToks (y.take p ++ (c, some t) :: y.drop p)) := by
                nth_rewrite 1 [← List.take_append_drop p y]
                rw [hhap, hhap, hhcs]
                apply List.perm_iff_count.2
                intro z
                simp only [List.count_append, List.count_cons, List.count_nil]
                omega
              have hlen : (y.take p ++ (c, some t) :: y.drop p).length = y.length + 1 := by
                have e1 : (y.take p ++ y.drop p).length = y.length := by rw [List.take_append_drop]
                rw [List.length_append] at e1
                rw [List.length_append, List.length_cons]
                omega
              have hlam : lamIn (y.take p ++ (c, some t) :: y.drop p) = lamIn y := by
                rw [hlamap, hlams, ← hlamap, List.take_append_drop]
              rw [hins, hmap, hPi', hlen, hlam, ← h1 _ _ hn hperm, hpl, List.append_nil, ← hetac y.length]
              ring
            rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hG2 y [] t c (by rw [hhnil, List.append_nil]; exact hn)
              (hhead y hy), hWnil, hPi' y]
            ring
          · intro a b g hy c g'
            have hn : (heldToks a ++ [t] ++ heldToks b).Nodup := by
              have := hy.1
              rw [hhap, hhcs] at this
              rw [List.append_assoc]
              exact this
            have hha : ∀ e u, a = e :: u → e.2 ≠ none := by
              intro e u hau
              exact hhead _ hy e (u ++ (g, some t) :: b) (by rw [hau]; rfl)
            have hW1 : W [] a * W (heldToks a ++ [t]) ((g', none) :: b) = W [] (a ++ (g, some t) :: b) := by
              have e1 : heldToks [(g', (none : Option T))] = [] := rfl
              have e2 : heldToks [(g, some t)] = [t] := rfl
              rw [hWap, hWcons, hWcons, e1, e2, List.append_nil, List.nil_append]
            have hterm : ∀ p ∈ range (a.length + 1),
                P.eta ((a ++ (g, some t) :: b).length + 1) * P.s (heldToks (a.take p) ++ [t]) *
                  Pi (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b)) =
                (P.lam g' * (piLam P (heldToks (a ++ (g, some t) :: b)) * lamIn (a ++ (g, some t) :: b) *
                  ∏ q ∈ range (a ++ (g, some t) :: b).length, (P.eta (q + 1))⁻¹)) *
                  (P.s (heldToks (a.take p) ++ [t]) *
                  W [] (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b))) := by
              intro p hp
              have hperm : (heldToks (a ++ (g, some t) :: b)).Perm
                  (heldToks (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b))) := by
                nth_rewrite 1 [← List.take_append_drop p a]
                rw [hhap, hhap, hhap, hhcs, hhcs, hhap, hhcn]
                apply List.perm_iff_count.2
                intro z
                simp only [List.count_append, List.count_cons]
                omega
              have hlen : (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b)).length =
                  (a ++ (g, some t) :: b).length + 1 := by
                have e1 : (a.take p ++ a.drop p).length = a.length := by rw [List.take_append_drop]
                rw [List.length_append] at e1
                rw [List.length_append, List.length_cons, List.length_append, List.length_cons,
                  List.length_append, List.length_cons]
                omega
              have hlam : lamIn (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b)) =
                  P.lam g' * lamIn (a ++ (g, some t) :: b) := by
                nth_rewrite 3 [← List.take_append_drop p a]
                rw [hlamap, hlams, hlamap, hlamn, hlamap, hlams, hlamap]
                ring
              rw [hPi', hlen, hlam, ← h1 _ _ hy.1 hperm, ← hetac (a ++ (g, some t) :: b).length]
              ring
            rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hG2 a ((g', none) :: b) t c
              (by rw [hhcn]; exact hn) hha, hW1, hPi' (a ++ (g, some t) :: b)]
            ring
        have L7C : ∀ (ins : ℕ → C → T → CState C T → CState C T)
          (hins : ∀ p c t y, ins p c t y = y.take p ++ (c, some t) ::
            (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e))
          (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (Pi : CState C T → ℝ)
          (hPi : ∀ y, Pi y = piLam P (heldToks y) * lamIn y *
            (∏ q ∈ range y.length, (kfun P (heldToks (y.take (q + 1))))⁻¹) *
            ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹)
          (wd : CState C T → List (Option C × Option T))
          (hwd : ∀ y, wd y = y.map (fun e => (if e.2 = none then some e.1 else none, e.2)))
          (hA7 : ∀ (y : CState C T) (c : C) (t : T), Valid P y → t ∉ held y →
            ∑ p ∈ range (y.length + 1), P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * Pi (ins p c t y)
              = lamTok P (held y) t * Pi y)
          (hB7 : ∀ (a b : CState C T) (g : C) (t : T) (c g' : C), Valid P (a ++ (g, some t) :: b) →
            ∑ p ∈ range (a.length + 1), P.eta ((a ++ (g, some t) :: b).length + 1) * P.s (heldToks (a.take p) ++ [t]) *
              Pi (a.take p ++ (c, some t) :: (a.drop p ++ (g', none) :: b))
              = P.lam g' * Pi (a ++ (g, some t) :: b))
          (f : CState C T → ℝ)
          (hf0 : ∀ y, 0 ≤ f y)
          (hfv : ∀ y, ¬ Valid P y → f y = 0)
          (k : ℝ)
          (hk0 : 0 ≤ k)
          (ih : ∀ y (F : Finset (CState C T)), (∀ y1 ∈ F, wd y1 = wd y) → ∑ y1 ∈ F, f y1 ≤ k * Pi y)
          (y : CState C T)
          (hy : Valid P y)
          (F : Finset (CState C T))
          (hF : ∀ y1 ∈ F, Valid P y1 ∧ wd y1 = wd y),
          ∑ y1 ∈ F, ∑ p ∈ range (y1.length + 1), ∑ c, ∑ t,
            P.eta (y1.length + 1) * P.s (heldToks (y1.take p) ++ [t]) * f (ins p c t y1) ≤ k * Pi y * lamTot P := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro ins hins lamIn hlamIn Pi hPi wd hwd hA7 hB7 f hf0 hfv k hk0 ih y hy F hF
          classical
          obtain ⟨hl0, htn, ha0, haz, ha1, hs0, heta⟩ := hS
          rcases isEmpty_or_nonempty C with hC | ⟨⟨c0⟩⟩
          · simp [lamTot]
          -- word facts
          have hlen : ∀ u v : CState C T, wd u = wd v → u.length = v.length := by
            intro u v h
            have := congrArg List.length h
            simpa [hwd] using this
          have hht : ∀ u v : CState C T, wd u = wd v → heldToks u = heldToks v := by
            intro u v h
            have e : ∀ u : CState C T, heldToks u = (wd u).filterMap Prod.snd := by
              intro u
              rw [hwd, List.filterMap_map]
              rfl
            rw [e, e, h]
          have hwt : ∀ (u v : CState C T) (p : ℕ), wd u = wd v → wd (u.take p) = wd (v.take p) := by
            intro u v p h
            rw [hwd, hwd] at *
            rw [List.map_take, List.map_take, h]
          have hwdr : ∀ (u v : CState C T) (p : ℕ), wd u = wd v → wd (u.drop p) = wd (v.drop p) := by
            intro u v p h
            rw [hwd, hwd] at *
            rw [List.map_drop, List.map_drop, h]
          have hwapp : ∀ (u v : CState C T), wd (u ++ v) = wd u ++ wd v := by
            intro u v; simp [hwd]
          have hwcons : ∀ (e : C × Option T) (v : CState C T),
              wd (e :: v) = (if e.2 = none then some e.1 else none, e.2) :: wd v := by
            intro u v; simp [hwd]
          have hmid : ∀ (u : CState C T) (t : T), t ∉ heldToks u →
              u.map (fun e => if e.2 = some t then (e.1, none) else e) = u := by
            intro u t ht
            conv_rhs => rw [← List.map_id u]
            apply List.map_congr_left
            intro e he
            have : e.2 ≠ some t := by
              intro h2
              exact ht (List.mem_filterMap.2 ⟨e, he, h2⟩)
            simp [this]
          have hhapp : ∀ u v : CState C T, heldToks (u ++ v) = heldToks u ++ heldToks v := by
            intro u v; simp [heldToks, List.filterMap_append]
          have hhcs : ∀ (c : C) (t : T) (v : CState C T), heldToks ((c, some t) :: v) = t :: heldToks v := by
            intro c t v; simp [heldToks]
          have hhcn : ∀ (c : C) (v : CState C T), heldToks ((c, none) :: v) = heldToks v := by
            intro c v; simp [heldToks]
          -- the weights
          obtain ⟨w, hw⟩ : ∃ w : C → T → ℝ, ∀ c t, w c t = if t ∈ held y then
              (if ∃ (a b : CState C T) (g0 : C), y = a ++ (g0, some t) :: b ∧ t ∈ P.tok c ∧
                P.tok c ⊆ insert t (held a) then 1 else 0) else P.assign c (held y) t := ⟨_, fun _ _ => rfl⟩
          have hW : ∀ c, ∑ t, w c t ≤ 1 := by
            intro c
            have hsub : ∀ (a b : CState C T) (g0 : C) (t : T), y = a ++ (g0, some t) :: b →
                insert t (held a) ⊆ held y := by
              intro a b g0 t h u hu
              rw [h]
              simp only [held, hhapp, hhcs, List.mem_toFinset, Finset.mem_insert, List.mem_append,
                List.mem_cons] at hu ⊢
              rcases hu with h|h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
            by_cases hc : P.tok c ⊆ held y
            · have hne : ∀ t, w c t ≠ 0 → w c t = 1 ∧ ∃ (a b : CState C T) (g0 : C),
                  y = a ++ (g0, some t) :: b ∧ t ∈ P.tok c ∧ P.tok c ⊆ insert t (held a) := by
                intro t h
                rw [hw] at h ⊢
                by_cases h1 : t ∈ held y
                · rw [if_pos h1] at h ⊢
                  split_ifs at h ⊢ with h2
                  · exact ⟨rfl, h2⟩
                  · exact absurd rfl h
                · rw [if_neg h1] at h
                  exact absurd (haz c _ t (by
                    rw [Finset.mem_sdiff]; rintro ⟨h3, _⟩; exact h1 (hc h3))) h
              have hU : ∀ (a b b' as : CState C T) (g0 g0' : C) (t t' : T),
                  y = (a ++ as) ++ (g0', some t') :: b' →
                  (g0, some t) :: b = as ++ (g0', some t') :: b' → P.tok c ⊆ insert t (held a) →
                  t' ∈ P.tok c → t = t' := by
                intro a b b' as g0 g0' t t' h1 h2 h3 h4
                rcases as with _ | ⟨e, d⟩
                · simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, Option.some.injEq] at h2
                  exact h2.1.2
                · simp only [List.cons_append, List.cons.injEq] at h2
                  have hnd := hy.1
                  rw [h1, hhapp, hhapp, ← h2.1, hhcs, hhcs] at hnd
                  have h5 := h3 h4
                  rw [Finset.mem_insert] at h5
                  rcases h5 with h5 | h5
                  · exact h5.symm
                  · exfalso
                    have h6 : t' ∈ heldToks a := by simpa [held] using h5
                    have h7 := (List.nodup_append.1 hnd).2.2
                    exact h7 t' (by simp [h6]) t' (by simp) rfl
              by_cases hz : ∀ t, w c t = 0
              · rw [Finset.sum_eq_zero fun t _ => hz t]; norm_num
              · rw [not_forall] at hz
                obtain ⟨t0, ht0⟩ := hz
                rw [Finset.sum_eq_single t0, (hne t0 ht0).1]
                · intro t _ htt
                  by_contra hwt0
                  apply htt
                  obtain ⟨-, a, b, g0, e1, e2, e3⟩ := hne t hwt0
                  obtain ⟨-, a', b', g0', e1', e2', e3'⟩ := hne t0 ht0
                  have e := e1.symm.trans e1'
                  rw [List.append_eq_append_iff] at e
                  rcases e with ⟨as, ea, eb⟩ | ⟨as, ea, eb⟩
                  · exact hU a b b' as g0 g0' t t0 (by rw [← ea]; exact e1') eb e3 e2'
                  · exact (hU a' b' b as g0' g0 t0 t (by rw [← ea]; exact e1) eb e3' e2).symm
                · intro h; exact absurd (Finset.mem_univ _) h
            · have hne : (P.tok c \ held y).Nonempty := by
                rw [Finset.sdiff_nonempty]; exact hc
              rw [← ha1 c _ hne]
              rw [← Finset.sum_subset (Finset.subset_univ (P.tok c \ held y))]
              · apply Finset.sum_le_sum
                intro t ht
                rw [hw, if_neg (Finset.mem_sdiff.1 ht).2]
              · intro t _ ht
                rw [hw]
                by_cases h1 : t ∈ held y
                · rw [if_pos h1, if_neg]
                  rintro ⟨a, b, g0, e1, e2, e3⟩
                  exact hc (e3.trans (hsub a b g0 t e1))
                · rw [if_neg h1]
                  exact haz c _ t ht
          obtain ⟨E, hE⟩ : ∃ E : ℕ → T → ℝ, ∀ p t, E p t = P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) :=
            ⟨_, fun _ _ => rfl⟩
          have hE0 : ∀ p t, 0 ≤ E p t := by
            intro p t
            rw [hE]
            exact mul_nonneg (heta _ (by omega)).le (hs0 _)
          have hPi0 : 0 ≤ k * Pi y := by
            simpa using ih y ∅ (by simp)
          have hB : ∀ t, ∑ p ∈ range (y.length + 1), E p t * ∑ x ∈ F ×ˢ (univ : Finset C), f (ins p x.2 t x.1)
              ≤ k * Pi y * ∑ c, P.lam c * w c t := by
            intro t
            by_cases ht : t ∈ held y
            · have h1 : (some t) ∈ y.map Prod.snd := by
                have h2 : t ∈ heldToks y := by simpa [held] using ht
                obtain ⟨e, he, h3⟩ := List.mem_filterMap.1 h2
                exact List.mem_map.2 ⟨e, he, h3⟩
              obtain ⟨⟨g, o⟩, he, ho⟩ := List.mem_map.1 h1
              simp only at ho
              subst ho
              obtain ⟨a, b, hyab⟩ := List.append_of_mem he
              have hnd := hy.1
              rw [hyab, hhapp, hhcs] at hnd
              have hta : t ∉ heldToks a := by
                intro h
                exact (List.nodup_append.1 hnd).2.2 t h t (by simp) rfl
              have htb : t ∉ heldToks b := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
              have hylen : y.length = a.length + b.length + 1 := by
                rw [hyab]; simp; omega
              have hsplit : ∀ y1 ∈ F, ∃ a1 g1 b1, y1 = a1 ++ (g1, some t) :: b1 ∧ wd a1 = wd a ∧
                  wd b1 = wd b := by
                intro y1 hy1
                have h := (hF y1 hy1).2
                rw [hyab, hwapp, hwcons, hwd y1, List.map_eq_append_iff] at h
                obtain ⟨l1, l2, h2, h3, h4⟩ := h
                rw [List.map_eq_cons_iff] at h4
                obtain ⟨e, l3, h5, h6, h7⟩ := h4
                have h8 : e.2 = some t := (Prod.mk.injEq .. ▸ h6).2
                refine ⟨l1, e.1, l3, ?_, ?_, ?_⟩
                · rw [h2, h5, ← h8]
                · rw [hwd l1]; exact h3
                · rw [hwd l3]; exact h7
              have hdropn : ∀ (u : CState C T) (p : ℕ), t ∉ heldToks u → t ∉ heldToks (u.drop p) := by
                intro u p h h2
                apply h
                rw [← List.take_append_drop p u, hhapp]
                exact List.mem_append_right _ h2
              have hinsB : ∀ (a1 b1 : CState C T) (g1 c : C) (p : ℕ), wd a1 = wd a → wd b1 = wd b →
                  p ≤ a.length → ins p c t (a1 ++ (g1, some t) :: b1) =
                  a1.take p ++ (c, some t) :: (a1.drop p ++ (g1, none) :: b1) := by
                intro a1 b1 g1 c p e1 e2 hp
                have hl := hlen _ _ e1
                rw [hins, List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
                  List.map_append, hmid _ _ (hdropn _ p (by rw [hht _ _ e1]; exact hta)), List.map_cons,
                  hmid _ _ (by rw [hht _ _ e2]; exact htb), if_pos rfl]
              have hzero : ∀ p ∈ range (y.length + 1), p ∉ range (a.length + 1) →
                  E p t * ∑ x ∈ F ×ˢ (univ : Finset C), f (ins p x.2 t x.1) = 0 := by
                intro p _ hp
                rw [Finset.mem_range, not_lt] at hp
                rw [Finset.sum_eq_zero, mul_zero]
                rintro ⟨y1, c⟩ hx
                obtain ⟨a1, g1, b1, e1, e2, e3⟩ := hsplit y1 (Finset.mem_product.1 hx).1
                have hl := hlen _ _ e2
                apply hfv
                intro hv
                have h2 := hv.1
                simp only at h2
                obtain ⟨q, rfl⟩ : ∃ q, p = a1.length + (q + 1) := ⟨p - a1.length - 1, by omega⟩
                rw [hins, e1, List.take_length_add_append, List.take_succ_cons, hhapp, hhcs, hhapp, hhcs] at h2
                exact (List.nodup_append.1 h2).2.2 t (by simp) t (by simp) rfl
              have hG : ∀ p ∈ range (a.length + 1), ∑ x ∈ F ×ˢ (univ : Finset C), f (ins p x.2 t x.1) ≤
                  ∑ g', w g' t * (k * Pi (a.take p ++ (c0, some t) :: (a.drop p ++ (g', none) :: b))) := by
                intro p hp
                have hp' : p ≤ a.length := by rw [Finset.mem_range] at hp; omega
                rw [← Finset.sum_image (f := f) (g := fun x : CState C T × C => ins p x.2 t x.1)]
                · rw [← Finset.sum_fiberwise _ (fun z : CState C T => (z[a.length + 1]?.map Prod.fst).getD c0)]
                  apply Finset.sum_le_sum
                  intro g' _
                  have hform : ∀ z ∈ Finset.filter (fun z : CState C T => (z[a.length + 1]?.map Prod.fst).getD c0 = g')
                      (Finset.image (fun x : CState C T × C => ins p x.2 t x.1) (F ×ˢ (univ : Finset C))),
                      ∃ a1 b1 c, z = a1.take p ++ (c, some t) :: (a1.drop p ++ (g', none) :: b1) ∧ wd a1 = wd a ∧
                        wd b1 = wd b ∧ t ∈ P.tok g' := by
                    intro z hz
                    rw [Finset.mem_filter, Finset.mem_image] at hz
                    obtain ⟨⟨⟨y1, c⟩, hx, hz1⟩, hz2⟩ := hz
                    have hy1 := (Finset.mem_product.1 hx).1
                    obtain ⟨a1, g1, b1, e1, e2, e3⟩ := hsplit y1 hy1
                    have hl := hlen _ _ e2
                    simp only at hz1 e1 hy1
                    rw [e1, hinsB a1 b1 g1 c p e2 e3 hp'] at hz1
                    have hgg : g1 = g' := by
                      rw [← hz2, ← hz1]
                      have h3 : (a1.take p ++ (c, some t) :: (a1.drop p ++ (g1, none) :: b1))
                          = (a1.take p ++ (c, some t) :: a1.drop p) ++ (g1, none) :: b1 := by simp
                      rw [h3, List.getElem?_append_right (by simp; omega)]
                      have h4 : a.length + 1 - (a1.take p ++ (c, some t) :: a1.drop p).length = 0 := by
                        simp; omega
                      rw [h4]
                      simp
                    subst hgg
                    refine ⟨a1, b1, c, hz1.symm, e2, e3, ?_⟩
                    have hv := (hF y1 hy1).1.2.1
                    subst e1
                    have h5 := hv a1.length (by simp) t (by simp)
                    simpa using h5
                  by_cases hc : t ∈ P.tok g' ∧ P.tok g' ⊆ insert t (held a)
                  · have hw1 : w g' t = 1 := by
                      rw [hw, if_pos ht, if_pos ⟨a, b, g, hyab, hc⟩]
                    rw [hw1, one_mul]
                    apply ih
                    intro z hz
                    obtain ⟨a1, b1, c, e1, e2, e3, -⟩ := hform z hz
                    rw [e1, hwapp, hwapp, hwcons, hwcons, hwapp, hwapp, hwcons, hwcons, e3,
                      hwt _ _ p e2, hwdr _ _ p e2]
                    rfl
                  · have hw0 : w g' t = 0 := by
                      rw [hw, if_pos ht, if_neg]
                      rintro ⟨a', b', g0, f1, f2, f3⟩
                      apply hc
                      have hta' : t ∉ heldToks a' := by
                        have hnd' := hy.1
                        rw [f1, hhapp, hhcs] at hnd'
                        intro h
                        exact (List.nodup_append.1 hnd').2.2 t h t (by simp) rfl
                      have haa : a' = a := by
                        have e := f1.symm.trans hyab
                        rw [List.append_eq_append_iff] at e
                        rcases e with ⟨as, ea, eb⟩ | ⟨as, ea, eb⟩
                        · rcases as with _ | ⟨x, d⟩
                          · simpa using ea.symm
                          · exfalso
                            simp only [List.cons_append, List.cons.injEq] at eb
                            apply hta
                            rw [ea, ← eb.1, hhapp, hhcs]; simp
                        · rcases as with _ | ⟨x, d⟩
                          · simpa using ea
                          · exfalso
                            simp only [List.cons_append, List.cons.injEq] at eb
                            apply hta'
                            rw [ea, ← eb.1, hhapp, hhcs]; simp
                      rw [haa] at f3
                      exact ⟨f2, f3⟩
                    rw [hw0, zero_mul]
                    apply le_of_eq
                    apply Finset.sum_eq_zero
                    intro z hz
                    obtain ⟨a1, b1, c, e1, e2, e3, e4⟩ := hform z hz
                    apply hfv
                    intro hv
                    apply hc
                    refine ⟨e4, ?_⟩
                    have hl := hlen _ _ e2
                    have h3 : z = (a1.take p ++ (c, some t) :: a1.drop p) ++ (g', none) :: b1 := by
                      rw [e1]; simp
                    have h4 : (a1.take p ++ (c, some t) :: a1.drop p).length < z.length := by
                      rw [h3]; simp
                    have h5 := hv.2.2 _ h4
                    have h6 : z[(a1.take p ++ (c, some t) :: a1.drop p).length]'h4 = (g', none) := by
                      simp only [h3]
                      rw [List.getElem_append_right le_rfl]
                      simp
                    rw [h6] at h5
                    have h7 : z.take (a1.take p ++ (c, some t) :: a1.drop p).length
                        = a1.take p ++ (c, some t) :: a1.drop p := by
                      rw [h3]; exact List.take_left
                    rw [h7] at h5
                    intro u hu
                    have h8 := h5 rfl hu
                    simp only [held, hhapp, hhcs, List.mem_toFinset, List.mem_append, List.mem_cons] at h8
                    rw [Finset.mem_insert, held, List.mem_toFinset, ← hht _ _ e2,
                      ← List.take_append_drop p a1, hhapp, List.mem_append]
                    rcases h8 with h|h|h
                    · exact Or.inr (Or.inl h)
                    · exact Or.inl h
                    · exact Or.inr (Or.inr h)
                · rintro ⟨y1, c⟩ hx ⟨y2, c'⟩ hx' heq
                  have hy1 := (Finset.mem_product.1 (Finset.mem_coe.1 hx)).1
                  have hy2 := (Finset.mem_product.1 (Finset.mem_coe.1 hx')).1
                  obtain ⟨a1, g1, b1, e1, e2, e3⟩ := hsplit y1 hy1
                  obtain ⟨a2, g2, b2, e1', e2', e3'⟩ := hsplit y2 hy2
                  have hl := hlen _ _ e2
                  have hl' := hlen _ _ e2'
                  simp only at e1 e1' heq
                  rw [e1, e1', hinsB a1 b1 g1 c p e2 e3 hp', hinsB a2 b2 g2 c' p e2' e3' hp'] at heq
                  obtain ⟨q1, q2⟩ := List.append_inj heq (by simp; omega)
                  rw [List.cons.injEq] at q2
                  obtain ⟨q3, q4⟩ := q2
                  obtain ⟨q5, q6⟩ := List.append_inj q4 (by simp; omega)
                  rw [List.cons.injEq] at q6
                  have q7 : a1 = a2 := by
                    rw [← List.take_append_drop p a1, ← List.take_append_drop p a2, q1, q5]
                  have q8 : g1 = g2 := congrArg Prod.fst q6.1
                  have q9 : c = c' := congrArg Prod.fst q3
                  rw [e1, e1', q7, q8, q9, q6.2]
              rw [← Finset.sum_subset (Finset.range_mono (by omega : a.length + 1 ≤ y.length + 1)) hzero]
              calc _ ≤ ∑ p ∈ range (a.length + 1), E p t *
                    ∑ g', w g' t * (k * Pi (a.take p ++ (c0, some t) :: (a.drop p ++ (g', none) :: b))) :=
                    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hG p hp) (hE0 p t)
                _ = ∑ g', w g' t * k * ∑ p ∈ range (a.length + 1), E p t *
                    Pi (a.take p ++ (c0, some t) :: (a.drop p ++ (g', none) :: b)) := by
                  simp only [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
                _ = k * Pi y * ∑ c, P.lam c * w c t := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun g' _ => ?_
                  have h7 : ∑ p ∈ range (a.length + 1), E p t *
                      Pi (a.take p ++ (c0, some t) :: (a.drop p ++ (g', none) :: b)) = P.lam g' * Pi y := by
                    have h8 := hB7 a b g t c0 g' (hyab ▸ hy)
                    rw [← hyab] at h8
                    rw [← h8]
                    refine Finset.sum_congr rfl fun p hp => ?_
                    have hp' : p ≤ a.length := by rw [Finset.mem_range] at hp; omega
                    rw [hE]
                    congr 4
                    rw [hyab, List.take_append_of_le_length hp']
                  rw [h7]; ring
            · have ht' : t ∉ heldToks y := by simpa [held] using ht
              have hdropn : ∀ (u : CState C T) (p : ℕ), t ∉ heldToks u → t ∉ heldToks (u.drop p) := by
                intro u p h h2
                apply h
                rw [← List.take_append_drop p u, hhapp]
                exact List.mem_append_right _ h2
              have hinsA : ∀ (u : CState C T) (c : C) (p : ℕ), wd u = wd y →
                  ins p c t u = u.take p ++ (c, some t) :: u.drop p := by
                intro u c p e1
                rw [hins, hmid _ _ (hdropn _ p (by rw [hht _ _ e1]; exact ht'))]
              have hG : ∀ p, ∑ x ∈ F ×ˢ (univ : Finset C), f (ins p x.2 t x.1) ≤ k * Pi (ins p c0 t y) := by
                intro p
                rw [← Finset.sum_image (f := f) (g := fun x : CState C T × C => ins p x.2 t x.1)]
                · apply ih
                  intro z hz
                  rw [Finset.mem_image] at hz
                  obtain ⟨⟨y1, c⟩, hx, hz1⟩ := hz
                  have hy1 := (hF y1 (Finset.mem_product.1 hx).1).2
                  simp only at hz1
                  rw [← hz1, hinsA _ _ _ hy1, hinsA _ _ _ rfl, hwapp, hwapp, hwcons, hwcons,
                    hwt _ _ p hy1, hwdr _ _ p hy1]
                  rfl
                · rintro ⟨y1, c⟩ hx ⟨y2, c'⟩ hx' heq
                  have hy1 := (hF y1 (Finset.mem_product.1 (Finset.mem_coe.1 hx)).1).2
                  have hy2 := (hF y2 (Finset.mem_product.1 (Finset.mem_coe.1 hx')).1).2
                  have hl := hlen _ _ hy1
                  have hl' := hlen _ _ hy2
                  simp only at heq
                  rw [hinsA _ _ _ hy1, hinsA _ _ _ hy2] at heq
                  obtain ⟨q1, q2⟩ := List.append_inj heq (by simp; omega)
                  rw [List.cons.injEq] at q2
                  have q7 : y1 = y2 := by
                    rw [← List.take_append_drop p y1, ← List.take_append_drop p y2, q1, q2.2]
                  have q9 : c = c' := congrArg Prod.fst q2.1
                  rw [q7, q9]
              calc _ ≤ ∑ p ∈ range (y.length + 1), E p t * (k * Pi (ins p c0 t y)) :=
                    Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hG p) (hE0 p t)
                _ = k * ∑ p ∈ range (y.length + 1), P.eta (y.length + 1) *
                      P.s (heldToks (y.take p) ++ [t]) * Pi (ins p c0 t y) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun p _ => ?_
                  rw [hE]; ring
                _ = k * Pi y * ∑ c, P.lam c * w c t := by
                  rw [hA7 y c0 t hy ht, lamTok]
                  have h7 : ∀ c, w c t = P.assign c (held y) t := by
                    intro c; rw [hw, if_neg ht]
                  simp only [h7]
                  ring
          have hmain : ∑ y1 ∈ F, ∑ p ∈ range (y1.length + 1), ∑ c, ∑ t,
              P.eta (y1.length + 1) * P.s (heldToks (y1.take p) ++ [t]) * f (ins p c t y1)
              = ∑ t, ∑ p ∈ range (y.length + 1), E p t * ∑ x ∈ F ×ˢ (univ : Finset C), f (ins p x.2 t x.1) := by
            have e1 : ∀ y1 ∈ F, ∑ p ∈ range (y1.length + 1), ∑ c, ∑ t,
              P.eta (y1.length + 1) * P.s (heldToks (y1.take p) ++ [t]) * f (ins p c t y1)
              = ∑ t, ∑ p ∈ range (y.length + 1), E p t * ∑ c, f (ins p c t y1) := by
              intro y1 hy1
              rw [hlen _ _ (hF y1 hy1).2, Finset.sum_comm (s := univ) (t := range (y.length + 1))]
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hE, ← Finset.mul_sum, hht _ _ (hwt _ _ p (hF y1 hy1).2)]
            rw [Finset.sum_congr rfl e1, Finset.sum_comm]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [← Finset.mul_sum, Finset.sum_product]
          rw [hmain]
          calc _ ≤ ∑ t, k * Pi y * ∑ c, P.lam c * w c t := Finset.sum_le_sum fun t _ => hB t
            _ = k * Pi y * ∑ c, P.lam c * ∑ t, w c t := by
              rw [← Finset.mul_sum, Finset.sum_comm]
              simp only [Finset.mul_sum]
            _ ≤ k * Pi y * lamTot P := by
              refine mul_le_mul_of_nonneg_left ?_ hPi0
              refine Finset.sum_le_sum fun c _ => ?_
              calc P.lam c * ∑ t, w c t ≤ P.lam c * 1 := mul_le_mul_of_nonneg_left (hW c) (hl0 c).le
                _ = P.lam c := mul_one _
        have L7D : ∀ (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (Pi : CState C T → ℝ)
          (hPi : ∀ y, Pi y = piLam P (heldToks y) * lamIn y *
            (∏ q ∈ range y.length, (kfun P (heldToks (y.take (q + 1))))⁻¹) *
            ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹)
          (wd : CState C T → List (Option C × Option T))
          (hwd : ∀ y, wd y = y.map (fun e => (if e.2 = none then some e.1 else none, e.2)))
          (R : CState C T → ℝ)
          (hR0 : R [] = 0)
          (hRn : ∀ y c, R (y ++ [(c, none)]) = P.lam c)
          (hRt : ∀ y c t, R (y ++ [(c, some t)]) = P.lam c * P.assign c (held y) t)
          (f : CState C T → ℝ)
          (hf0 : ∀ y, 0 ≤ f y)
          (hfv : ∀ y, ¬ Valid P y → f y = 0)
          (k : ℝ)
          (hk0 : 0 ≤ k)
          (ih : ∀ y (F : Finset (CState C T)), (∀ y1 ∈ F, wd y1 = wd y) → ∑ y1 ∈ F, f y1 ≤ k * Pi y)
          (y : CState C T)
          (hy : Valid P y)
          (F : Finset (CState C T))
          (hF : ∀ y1 ∈ F, Valid P y1 ∧ wd y1 = wd y),
          ∑ y1 ∈ F, R y1 * f y1.dropLast ≤ k * Pi y * (P.eta y.length * kfun P (heldToks y)) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro lamIn hlamIn Pi hPi wd hwd R hR0 hRn hRt f hf0 hfv k hk0 ih y hy F hF
          classical
          obtain ⟨hlam, htok, has0, has1, has2, hs0, heta⟩ := id hS
          have gen : ∀ (A : Type) (l : List A) (a : A) (F : ℕ → A → ℝ),
              ∏ j : Fin (l ++ [a]).length, F j ((l ++ [a]).get j)
                = (∏ j : Fin l.length, F j (l.get j)) * F l.length a := by
            intro A l a F
            have hl : (l ++ [a]).length = l.length + 1 := by simp
            rw [← Equiv.prod_comp (finCongr hl.symm), Fin.prod_univ_castSucc]
            simp
          have hPL : ∀ (l : List T) (t : T), piLam P (l ++ [t]) = piLam P l * lamTok P l.toFinset t := by
            intro l t
            unfold piLam
            rw [gen T l t (fun j a => lamTok P ((l ++ [t]).take j).toFinset a)]
            congr 1
            · refine Finset.prod_congr rfl fun j _ => ?_
              rw [List.take_append_of_le_length j.2.le]
            · simp
          -- one-step recursion for `Pi`
          have hPiS : ∀ (y0 : CState C T) (e : C × Option T),
              Pi (y0 ++ [e]) = piLam P (heldToks (y0 ++ [e])) * (lamIn y0 * (if e.2 = none then P.lam e.1 else 1)) *
                ((∏ q ∈ range y0.length, (kfun P (heldToks (y0.take (q + 1))))⁻¹) *
                  (kfun P (heldToks (y0 ++ [e])))⁻¹) *
                ((∏ q ∈ range y0.length, (P.eta (q + 1))⁻¹) * (P.eta (y0 ++ [e]).length)⁻¹) := by
            intro y0 e
            have hl : (y0 ++ [e]).length = y0.length + 1 := by simp
            have hli : lamIn (y0 ++ [e]) = lamIn y0 * (if e.2 = none then P.lam e.1 else 1) := by
              rw [hlamIn, hlamIn, List.map_append, List.prod_append]
              simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            have hpr : ∏ q ∈ range (y0.length + 1), (kfun P (heldToks ((y0 ++ [e]).take (q + 1))))⁻¹
                = (∏ q ∈ range y0.length, (kfun P (heldToks (y0.take (q + 1))))⁻¹) *
                  (kfun P (heldToks (y0 ++ [e])))⁻¹ := by
              rw [Finset.prod_range_succ]
              congr 1
              · refine Finset.prod_congr rfl fun q hq => ?_
                rw [List.take_append_of_le_length (Finset.mem_range.1 hq)]
              · rw [List.take_of_length_le hl.le]
            rw [hPi, hl, hli, hpr, Finset.prod_range_succ]
          have hwdh : ∀ z z' : CState C T, wd z = wd z' → heldToks z = heldToks z' := by
            have h3 : ∀ z : CState C T, heldToks z = (wd z).filterMap Prod.snd := by
              intro z
              rw [hwd, List.filterMap_map]
              rfl
            intro z z' h
            rw [h3 z, h3 z', h]
          have hwda : ∀ (z : CState C T) e, wd (z ++ [e]) = wd z ++ [(if e.2 = none then some e.1 else none, e.2)] := by
            intro z e
            rw [hwd, hwd, List.map_append]; rfl
          -- every member of F
          have hmem : ∀ (y0 : CState C T) e, y = y0 ++ [e] → ∀ y1 ∈ F, ∃ z e', y1 = z ++ [e'] ∧ wd z = wd y0 ∧
              e'.2 = e.2 ∧ (e.2 = none → e' = e) := by
            intro y0 e hye y1 hy1
            have hw := (hF y1 hy1).2
            rw [hye, hwda] at hw
            rcases List.eq_nil_or_concat y1 with h0 | ⟨z, e', h0⟩
            · exfalso
              rw [h0, hwd] at hw
              simp at hw
            · rw [List.concat_eq_append] at h0
              rw [h0, hwda] at hw
              obtain ⟨hw1, hw2⟩ := List.append_inj' hw rfl
              rw [List.cons.injEq, Prod.mk.injEq] at hw2
              obtain ⟨⟨hw3, hw4⟩, -⟩ := hw2
              refine ⟨z, e', h0, hw1, hw4, ?_⟩
              intro hn
              rw [hw4, if_pos hn, if_pos hn] at hw3
              exact Prod.ext (Option.some.inj hw3) hw4
          let F' : Finset (CState C T) := F.image List.dropLast
          have hdl : ∀ (z : CState C T) e, (z ++ [e]).dropLast = z := fun z e => List.dropLast_concat
          have hF' : ∀ (y0 : CState C T) e, y = y0 ++ [e] → ∀ z ∈ F', wd z = wd y0 := by
            intro y0 e hye z hz
            obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.1 hz
            obtain ⟨z, e', h0, hw, -, -⟩ := hmem y0 e hye y1 hy1
            rw [h0, hdl]; exact hw
          have hkp : y ≠ [] → 0 < kfun P (heldToks y) := by
            intro hne
            refine hk _ hy.1 ?_
            intro hh
            have hlen : 0 < y.length := List.length_pos_iff.2 hne
            have hh2 : heldToks y = [] := hh
            unfold heldToks at hh2
            rw [List.filterMap_eq_nil_iff] at hh2
            have hnone := hh2 (y[0]'hlen) (List.getElem_mem hlen)
            have h3 := hy.2.2 0 hlen hnone
            obtain ⟨t, ht⟩ := htok (y[0]'hlen).1
            have h4 := h3 ht
            simp [held, heldToks] at h4
          rcases List.eq_nil_or_concat y with hy0 | ⟨y0, e, hye⟩
          · have hz : ∀ y1 ∈ F, R y1 * f y1.dropLast = 0 := by
              intro y1 hy1
              have hw := (hF y1 hy1).2
              rw [hy0, hwd, hwd, List.map_nil, List.map_eq_nil_iff] at hw
              rw [hw, hR0, zero_mul]
            rw [Finset.sum_eq_zero hz, hy0]
            have : kfun P (heldToks ([] : CState C T)) = 0 := by simp [kfun, heldToks]
            rw [this, mul_zero, mul_zero]
          · rw [List.concat_eq_append] at hye
            have hne : y ≠ [] := by rw [hye]; simp
            have hkpos := hkp hne
            have hepos := heta y.length (List.length_pos_iff.2 hne)
            have hihF := ih y0 F' (hF' y0 e hye)
            obtain ⟨c0, o⟩ := e
            cases o with
            | none =>
              have hsub : F ⊆ F'.image (fun z => z ++ [(c0, (none : Option T))]) := by
                intro y1 hy1
                obtain ⟨z, e', h0, hw, -, h3⟩ := hmem y0 _ hye y1 hy1
                rw [Finset.mem_image]
                refine ⟨z, Finset.mem_image.2 ⟨y1, hy1, by rw [h0, hdl]⟩, ?_⟩
                rw [h0, h3 rfl]
              have hPy : Pi y * (P.eta y.length * kfun P (heldToks y)) = P.lam c0 * Pi y0 := by
                have hh : heldToks (y0 ++ [(c0, (none : Option T))]) = heldToks y0 := by
                  simp [heldToks]
                rw [hye] at hkpos hepos ⊢
                rw [hPiS, hPi y0]
                rw [if_pos rfl, hh]
                rw [hh] at hkpos
                have ab : ∀ a b l A K I E K' E' : ℝ, K' * K = 1 → E' * E = 1 →
                    a * (b * l) * (A * K') * (I * E') * (E * K) = l * (a * b * A * I) := by
                  intro a b l A K I E K' E' hK hE
                  linear_combination (a * b * l * A * I * E' * E) * hK + (a * b * l * A * I) * hE
                exact ab _ _ _ _ _ _ _ _ _ (inv_mul_cancel₀ hkpos.ne') (inv_mul_cancel₀ hepos.ne')
              calc ∑ y1 ∈ F, R y1 * f y1.dropLast
                  ≤ ∑ y1 ∈ F'.image (fun z => z ++ [(c0, (none : Option T))]), R y1 * f y1.dropLast := by
                    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
                    intro y1 hy1 _
                    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy1
                    rw [hRn]
                    exact mul_nonneg (hlam c0).le (hf0 _)
                _ = ∑ z ∈ F', P.lam c0 * f z := by
                    rw [Finset.sum_image (fun a _ b _ h => List.append_cancel_right h)]
                    refine Finset.sum_congr rfl fun z _ => ?_
                    rw [hRn, hdl]
                _ = P.lam c0 * ∑ z ∈ F', f z := by rw [Finset.mul_sum]
                _ ≤ P.lam c0 * (k * Pi y0) := mul_le_mul_of_nonneg_left hihF (hlam c0).le
                _ = k * Pi y * (P.eta y.length * kfun P (heldToks y)) := by
                    rw [mul_assoc k, hPy]; ring
            | some t =>
              have hsub : F ⊆ ((univ : Finset C) ×ˢ F').image (fun p => p.2 ++ [(p.1, some t)]) := by
                intro y1 hy1
                obtain ⟨z, e', h0, hw, h2, -⟩ := hmem y0 _ hye y1 hy1
                rw [Finset.mem_image]
                refine ⟨(e'.1, z), Finset.mem_product.2 ⟨Finset.mem_univ _,
                  Finset.mem_image.2 ⟨y1, hy1, by rw [h0, hdl]⟩⟩, ?_⟩
                have h5 : e' = (e'.1, some t) := Prod.ext rfl h2
                show z ++ [(e'.1, some t)] = y1
                rw [h0, ← h5]
              have hPy : Pi y * (P.eta y.length * kfun P (heldToks y)) = lamTok P (held y0) t * Pi y0 := by
                have hh : heldToks (y0 ++ [(c0, some t)]) = heldToks y0 ++ [t] := by
                  simp [heldToks]
                rw [hye] at hkpos hepos ⊢
                rw [hPiS, hPi y0]
                rw [if_neg (by simp), hh, hPL]
                rw [hh] at hkpos
                unfold held
                have ab : ∀ a b l A K I E K' E' : ℝ, K' * K = 1 → E' * E = 1 →
                    a * l * (b * 1) * (A * K') * (I * E') * (E * K) = l * (a * b * A * I) := by
                  intro a b l A K I E K' E' hK hE
                  linear_combination (a * b * l * A * I * E' * E) * hK + (a * b * l * A * I) * hE
                exact ab _ _ _ _ _ _ _ _ _ (inv_mul_cancel₀ hkpos.ne') (inv_mul_cancel₀ hepos.ne')
              calc ∑ y1 ∈ F, R y1 * f y1.dropLast
                  ≤ ∑ y1 ∈ ((univ : Finset C) ×ˢ F').image (fun p => p.2 ++ [(p.1, some t)]),
                      R y1 * f y1.dropLast := by
                    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
                    intro y1 hy1 _
                    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy1
                    rw [hRt]
                    exact mul_nonneg (mul_nonneg (hlam _).le (has0 _ _ _)) (hf0 _)
                _ = ∑ p ∈ (univ : Finset C) ×ˢ F', P.lam p.1 * P.assign p.1 (held y0) t * f p.2 := by
                    rw [Finset.sum_image]
                    · refine Finset.sum_congr rfl fun p hp => ?_
                      have hh : held p.2 = held y0 := by
                        unfold held
                        rw [hwdh _ _ (hF' y0 _ hye p.2 (Finset.mem_product.1 hp).2)]
                      rw [hRt, hdl, hh]
                    · rintro ⟨a1, a2⟩ _ ⟨b1, b2⟩ _ h
                      obtain ⟨h3, h4⟩ := List.append_inj' h rfl
                      rw [List.cons.injEq, Prod.mk.injEq] at h4
                      exact Prod.ext h4.1.1 h3
                _ = lamTok P (held y0) t * ∑ z ∈ F', f z := by
                    rw [Finset.sum_product]
                    unfold lamTok
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun c _ => ?_
                    rw [Finset.mul_sum]
                _ ≤ lamTok P (held y0) t * (k * Pi y0) := by
                    refine mul_le_mul_of_nonneg_left hihF ?_
                    exact Finset.sum_nonneg fun c _ => mul_nonneg (hlam c).le (has0 c _ t)
                _ = k * Pi y * (P.eta y.length * kfun P (heldToks y)) := by
                    rw [mul_assoc k, hPy]; ring
        have L10 : ∀ (B : ℕ → Finset (State T))
          (hB : ∀ n x, x ∈ B n ↔ phi x.1 = n),
          ∀ n, ∑ x ∈ B (n + 1), P.eta (n + 1) * kfun P (toks x.1) * weight P x ≤ lamTot P * ∑ x ∈ B n, weight P x := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro B hB
          obtain ⟨hlam, htok, has0, has1, has2, hs0, heta⟩ := id hS
          have kf0 : ∀ l : List T, 0 ≤ kfun P l := fun l => Finset.sum_nonneg fun j _ => hs0 _
          have lt0 : ∀ (S : Finset T) t, 0 ≤ lamTok P S t := fun S t =>
            Finset.sum_nonneg fun c _ => mul_nonneg (hlam c).le (has0 c S t)
          have lu0 : ∀ (S : Finset T), 0 ≤ lamU P S := fun S =>
            Finset.sum_nonneg fun c _ => (hlam c).le
          have w0 : ∀ x : List (T × ℕ), 0 ≤ weightL P x := by
            intro x
            unfold weightL
            refine mul_nonneg (mul_nonneg (div_nonneg ?_ ?_) ?_) ?_
            · exact Finset.prod_nonneg fun j _ => lt0 _ _
            · exact Finset.prod_nonneg fun j _ => kf0 _
            · exact Finset.prod_nonneg fun j _ => pow_nonneg (div_nonneg (lu0 _) (kf0 _)) _
            · exact Finset.prod_nonneg fun j hj => inv_nonneg.2 (heta j (Finset.mem_Icc.1 hj).1).le
          -- products over `Fin (l ++ [a]).length`
          have gen : ∀ (A : Type) (l : List A) (a : A) (F : ℕ → A → ℝ),
              ∏ j : Fin (l ++ [a]).length, F j ((l ++ [a]).get j)
                = (∏ j : Fin l.length, F j (l.get j)) * F l.length a := by
            intro A l a F
            have hl : (l ++ [a]).length = l.length + 1 := by simp
            rw [← Equiv.prod_comp (finCongr hl.symm), Fin.prod_univ_castSucc]
            simp
          have hPL : ∀ (l : List T) (t : T), piLam P (l ++ [t]) = piLam P l * lamTok P l.toFinset t := by
            intro l t
            unfold piLam
            rw [gen T l t (fun j a => lamTok P ((l ++ [t]).take j).toFinset a)]
            refine congrArg₂ (· * ·) ?_ ?_
            · refine Finset.prod_congr rfl fun j _ => ?_
              rw [List.take_append_of_le_length j.2.le]
            · simp
          have hPK : ∀ (l : List T) (t : T), piK P (l ++ [t]) = piK P l * kfun P (l ++ [t]) := by
            intro l t
            unfold piK
            rw [gen T l t (fun j a => kfun P ((l ++ [t]).take (j+1)))]
            refine congrArg₂ (· * ·) ?_ ?_
            · refine Finset.prod_congr rfl fun j _ => ?_
              rw [List.take_append_of_le_length j.2]
            · rw [List.take_of_length_le (by rw [List.length_append]; rfl)]
          have htk : ∀ (x : List (T × ℕ)) t m, toks (x ++ [(t, m)]) = toks x ++ [t] := by
            intro x t m; simp [toks]
          have hlen : ∀ (x : List (T × ℕ)), (toks x).length = x.length := by
            intro x; simp [toks]
          have hAl : ∀ (x : List (T × ℕ)) t m,
              (∏ j : Fin (x ++ [(t, m)]).length,
                  alpha P ((toks (x ++ [(t, m)])).take (j + 1)) ^ ((x ++ [(t, m)]).get j).2)
                = (∏ j : Fin x.length, alpha P ((toks x).take (j + 1)) ^ (x.get j).2) *
                  alpha P (toks x ++ [t]) ^ m := by
            intro x t m
            rw [gen (T × ℕ) x (t, m)
              (fun j a => alpha P ((toks (x ++ [(t, m)])).take (j + 1)) ^ a.2), htk]
            refine congrArg₂ (· * ·) ?_ ?_
            · refine Finset.prod_congr rfl fun j _ => ?_
              rw [List.take_append_of_le_length (by rw [hlen]; exact j.2)]
            · rw [List.take_of_length_le (by simp [hlen])]
          have hphi : ∀ (x : List (T × ℕ)) t m, phi (x ++ [(t, m)]) = phi x + m + 1 := by
            intro x t m
            simp only [phi, List.length_append, List.length_cons, List.length_nil, List.map_append,
              List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
            omega
          have hIcc : ∀ m : ℕ, ∏ j ∈ Icc 1 (m + 1), (P.eta j)⁻¹
              = (∏ j ∈ Icc 1 m, (P.eta j)⁻¹) * (P.eta (m + 1))⁻¹ := by
            intro m
            exact Finset.prod_Icc_succ_top (by omega) _
          have hW0 : ∀ (x : List (T × ℕ)) t, (toks x ++ [t]).Nodup →
              P.eta (phi x + 1) * kfun P (toks x ++ [t]) * weightL P (x ++ [(t, 0)])
                = weightL P x * lamTok P (toks x).toFinset t := by
            intro x t hn
            have hkp := hk _ hn (by simp)
            have he := heta (phi x + 1) (by omega)
            unfold weightL
            rw [hAl, htk, hPL, hPK, hphi, Nat.add_zero, hIcc, pow_zero, mul_div_mul_comm]
            have ab : ∀ e k r l A I e' d : ℝ, e' * e = 1 → d * k = l →
                e * k * (r * d * (A * 1) * (I * e')) = r * A * I * l := by
              intro e k r l A I e' d he hd
              linear_combination (r * A * I * e' * e) * hd + (r * A * I * l) * he
            exact ab _ _ _ _ _ _ _ _ (inv_mul_cancel₀ he.ne') (div_mul_cancel₀ _ hkp.ne')
          have hW1 : ∀ (x : List (T × ℕ)) t m, (toks x ++ [t]).Nodup →
              P.eta (phi (x ++ [(t, m)]) + 1) * kfun P (toks x ++ [t]) * weightL P (x ++ [(t, m + 1)])
                = weightL P (x ++ [(t, m)]) * lamU P (toks x ++ [t]).toFinset := by
            intro x t m hn
            have hkp := hk _ hn (by simp)
            have he := heta (phi (x ++ [(t, m)]) + 1) (by omega)
            have hp : phi (x ++ [(t, m + 1)]) = phi (x ++ [(t, m)]) + 1 := by
              rw [hphi, hphi]; omega
            have ha : alpha P (toks x ++ [t]) * kfun P (toks x ++ [t])
                = lamU P (toks x ++ [t]).toFinset := by
              unfold alpha; exact div_mul_cancel₀ _ hkp.ne'
            unfold weightL
            rw [hAl, hAl, htk, htk, hp, hIcc, pow_succ, ← ha]
            have ab : ∀ e k r A b a I e' : ℝ, e' * e = 1 →
                e * k * (r * (A * (b * a)) * (I * e')) = r * (A * b) * I * (a * k) := by
              intro e k r A b a I e' he
              linear_combination (k * r * A * b * a * I) * he
            exact ab _ _ _ _ _ _ _ _ (inv_mul_cancel₀ he.ne')
          have hmod : ∀ (x : List (T × ℕ)) t m, modLast (· + 1) (x ++ [(t, m)]) = x ++ [(t, m + 1)] := by
            intro x t m
            induction x with
            | nil => rfl
            | cons a x ih =>
              cases x with
              | nil => rfl
              | cons b x => 
                have : modLast (· + 1) (a :: b :: x ++ [(t, m)])
                  = a :: modLast (· + 1) (b :: x ++ [(t, m)]) := rfl
                rw [this, ih]; rfl
          have htot : ∀ S : Finset T, lamU P S + ∑ t ∈ univ \ S, lamTok P S t = lamTot P := by
            intro S
            unfold lamU lamTok lamTot
            rw [Finset.sum_comm, Finset.sum_filter, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← Finset.mul_sum]
            by_cases hc : P.tok c ⊆ S
            · rw [if_pos hc, Finset.sum_eq_zero, mul_zero, add_zero]
              intro t ht
              refine has1 c S t ?_
              rw [Finset.sdiff_eq_empty_iff_subset.2 hc]; simp
            · have h3 : ∑ t ∈ univ \ S, P.assign c S t = ∑ t ∈ P.tok c \ S, P.assign c S t := by
                symm
                refine Finset.sum_subset (Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl) ?_
                intro t _ ht
                exact has1 c S t ht
              rw [if_neg hc, h3, has2 c S (Finset.sdiff_nonempty.2 hc), mul_one, zero_add]
          intro n
          classical
          let G : List (T × ℕ) → ℝ := fun x =>
            if (toks x).Nodup then P.eta (n + 1) * kfun P (toks x) * weightL P x else 0
          have hG0 : ∀ x, 0 ≤ G x := by
            intro x
            simp only [G]
            split_ifs
            · exact mul_nonneg (mul_nonneg (heta _ (by omega)).le (kf0 _)) (w0 _)
            · exact le_rfl
          let g : State T × Option T → List (T × ℕ) := fun p =>
            match p.2 with
            | none => modLast (· + 1) p.1.1
            | some t => p.1.1 ++ [(t, 0)]
          have hE : ∑ x ∈ B (n + 1), P.eta (n + 1) * kfun P (toks x.1) * weight P x
              = ∑ x ∈ (B (n + 1)).image Subtype.val, G x := by
            rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [G]
            have hxn : (toks x.1).Nodup := x.2
            rw [if_pos hxn]; rfl
          have hsub : (B (n + 1)).image Subtype.val ⊆ ((B n) ×ˢ (univ : Finset (Option T))).image g := by
            intro z hz
            obtain ⟨⟨x, hx⟩, hxB, rfl⟩ := Finset.mem_image.1 hz
            have hph : phi x = n + 1 := (hB _ _).1 hxB
            rcases List.eq_nil_or_concat x with h0 | ⟨x0, ⟨t, m⟩, h0⟩
            · exfalso; rw [h0] at hph; simp [phi] at hph
            · rw [List.concat_eq_append] at h0
              rw [h0] at hph hx
              rw [hphi] at hph
              rw [Finset.mem_image]
              cases m with
              | zero =>
                refine ⟨(⟨x0, ?_⟩, some t), ?_, ?_⟩
                · rw [List.map_append] at hx
                  exact hx.of_append_left
                · rw [Finset.mem_product]
                  exact ⟨(hB _ _).2 (by show phi x0 = n; omega), Finset.mem_univ _⟩
                · exact h0.symm
              | succ m =>
                refine ⟨(⟨x0 ++ [(t, m)], ?_⟩, none), ?_, ?_⟩
                · rw [List.map_append] at hx ⊢
                  exact hx
                · rw [Finset.mem_product]
                  exact ⟨(hB _ _).2 (by show phi (x0 ++ [(t, m)]) = n; rw [hphi]; omega), Finset.mem_univ _⟩
                · show modLast (· + 1) (x0 ++ [(t, m)]) = x
                  rw [hmod, h0]
          have hle : ∀ (s : Finset (State T × Option T)), ∑ z ∈ s.image g, G z ≤ ∑ p ∈ s, G (g p) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.image_insert, Finset.sum_insert ha]
              by_cases hm : g a ∈ s.image g
              · rw [Finset.insert_eq_of_mem hm]
                linarith [hG0 (g a)]
              · rw [Finset.sum_insert hm]
                linarith
          rw [hE, Finset.mul_sum]
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hG0 z).trans ?_
          refine (hle _).trans ?_
          rw [Finset.sum_product]
          refine Finset.sum_le_sum fun x hx => ?_
          have hph : phi x.1 = n := (hB _ _).1 hx
          have hxn : (toks x.1).Nodup := x.2
          rw [Fintype.sum_option, ← htot (toks x.1).toFinset, add_mul]
          refine add_le_add ?_ ?_
          · show G (modLast (· + 1) x.1) ≤ lamU P (toks x.1).toFinset * weightL P x.1
            rcases List.eq_nil_or_concat x.1 with h0 | ⟨x0, ⟨t, m⟩, h0⟩
            · rw [h0]
              have : G (modLast (· + 1) []) = 0 := by
                simp [G, modLast, toks, kfun]
              rw [this]
              exact mul_nonneg (lu0 _) (w0 _)
            · rw [List.concat_eq_append] at h0
              rw [h0] at hph hxn ⊢
              rw [htk] at hxn
              rw [hmod]
              simp only [G]
              rw [htk, htk, if_pos hxn, ← hph, hW1 _ _ _ hxn, mul_comm]
          · show ∑ t : T, G (x.1 ++ [(t, 0)]) ≤ _
            rw [Finset.sum_mul, ← Finset.sum_subset (Finset.subset_univ (univ \ (toks x.1).toFinset))]
            · refine Finset.sum_le_sum fun t ht => ?_
              have htn : t ∉ toks x.1 := by simpa using ht
              have hnd : (toks x.1 ++ [t]).Nodup := by
                rw [List.nodup_append]
                refine ⟨hxn, List.nodup_singleton t, ?_⟩
                intro a ha b hb hab
                rw [List.mem_singleton] at hb
                exact htn (hb ▸ hab ▸ ha)
              simp only [G]
              rw [htk, if_pos hnd, ← hph, hW0 _ _ hnd, mul_comm]
              exact le_rfl
            · intro t _ ht
              have htn : t ∈ toks x.1 := by simpa using ht
              simp only [G]
              rw [htk, if_neg]
              intro hnd
              rw [List.nodup_append] at hnd
              exact hnd.2.2 t htn t (List.mem_singleton.2 rfl) rfl
        have L0a : ∀ (Y : (x : List (T × ℕ)) → (Fin x.length → C) → ((j : Fin x.length) → Fin (x.get j).2 → C) → CState C T)
          (hY : ∀ x cs l, Y x cs l = (List.finRange x.length).flatMap (fun j =>
            (cs j, some (x.get j).1) :: List.ofFn (fun m => (l j m, none)))),
          (∀ x cs l, blocks (Y x cs l) = List.ofFn (fun j => (cs j, (x.get j).1, List.ofFn (l j)))) ∧
          (∀ x cs l, desc (Y x cs l) = x) ∧
          (∀ x cs l, holderTypes (Y x cs l) = List.ofFn cs) ∧
          (∀ x cs l cs' l', Y x cs l = Y x cs' l' → cs = cs' ∧ l = l') ∧
          (∀ x y, Valid P y → desc y = x → ∃ cs l, y = Y x cs l) ∧
          (∀ x cs l, heldToks (Y x cs l) = toks x) ∧
          (∀ x cs l, (Y x cs l).length = phi x) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          clear hk
          clear h2
          clear h1
          intro Y hY
          have hne : ∀ c, (P.tok c).Nonempty := hS.2.1
          -- one step of the fold
          obtain ⟨stp, hstp⟩ : ∃ stp : List (C × T × List C) → C × Option T → List (C × T × List C),
              stp = fun acc p => match p.2 with
                | none => acc.modifyLast (fun b => (b.1, b.2.1, b.2.2 ++ [p.1]))
                | some t => acc ++ [(p.1, t, [])] := ⟨_, rfl⟩
          have hbl : ∀ y : CState C T, blocks y = y.foldl stp [] := by
            intro y; rw [hstp]; rfl
          have hstpN : ∀ acc g t (r : List C) c, stp (acc ++ [(g, t, r)]) (c, none) =
              acc ++ [(g, t, r ++ [c])] := by
            intro acc g t r c
            rw [hstp]
            simp [List.modifyLast_concat]
          have hstpS : ∀ acc c t, stp acc (c, some t) = acc ++ [(c, t, [])] := by
            intro acc c t; rw [hstp]
          have hin : ∀ (r' : List C) acc g t r,
              (r'.map (fun c => ((c, none) : C × Option T))).foldl stp (acc ++ [(g, t, r)]) =
                acc ++ [(g, t, r ++ r')] := by
            intro r'
            induction r' with
            | nil => intro acc g t r; simp
            | cons a r' ih =>
              intro acc g t r
              rw [List.map_cons, List.foldl_cons, hstpN, ih]
              simp
          -- flattening
          obtain ⟨fl, hfl⟩ : ∃ fl : List (C × T × List C) → CState C T,
              ∀ bs, fl bs = bs.flatMap (fun b => (b.1, some b.2.1) :: b.2.2.map (fun c => (c, none))) :=
            ⟨fun bs => bs.flatMap (fun b => (b.1, some b.2.1) :: b.2.2.map (fun c => (c, none))),
              fun _ => rfl⟩
          have hflf : ∀ bs acc, (fl bs).foldl stp acc = acc ++ bs := by
            intro bs
            simp only [hfl]
            induction bs with
            | nil => intro acc; simp
            | cons b bs ih =>
              intro acc
              obtain ⟨g, t, r⟩ := b
              rw [List.flatMap_cons, List.foldl_append, List.foldl_cons, hstpS, hin, ih]
              simp
          have hYfl : ∀ x cs l, Y x cs l =
              fl (List.ofFn (fun j => (cs j, (x.get j).1, List.ofFn (l j)))) := by
            intro x cs l
            rw [hY, hfl, List.ofFn_eq_map, List.flatMap_map]
            congr 1
            funext j
            simp only [List.map_ofFn]
            rfl
          have hB : ∀ x cs l, blocks (Y x cs l) =
              List.ofFn (fun j => (cs j, (x.get j).1, List.ofFn (l j))) := by
            intro x cs l
            rw [hbl, hYfl, hflf, List.nil_append]
          refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x cs l
            unfold desc
            rw [hB, List.map_ofFn]
            refine Eq.trans ?_ (List.ofFn_get x)
            congr 1
            funext j
            simp
          · intro x cs l
            unfold holderTypes
            rw [hB, List.map_ofFn]
            rfl
          · intro x cs l cs' l' h
            have h' := congrArg blocks h
            rw [hB, hB] at h'
            have h2 := List.ofFn_injective h'
            refine ⟨?_, ?_⟩
            · funext j
              exact congrArg Prod.fst (congrFun h2 j)
            · funext j
              exact List.ofFn_injective (congrArg (fun b => b.2.2) (congrFun h2 j))
          · intro x y hv hd
            have hfirst : y = fl (blocks y) := by
              have key : ∀ z : CState C T, (z = [] ∨ ∃ c t z', z = (c, some t) :: z') → 
                  z = fl (blocks z) ∧ (z ≠ [] → blocks z ≠ []) := by
                intro z
                induction z using List.reverseRecOn with
                | nil => intro _; rw [hbl, hfl]; simp
                | append_singleton z e ih =>
                  intro hz
                  have hstep : blocks (z ++ [e]) = stp (blocks z) e := by
                    rw [hbl, hbl, List.foldl_append]; rfl
                  obtain ⟨c, o⟩ := e
                  have hz' : z = [] ∨ ∃ c t z', z = (c, some t) :: z' := by
                    rcases z with _ | ⟨a, z⟩
                    · exact Or.inl rfl
                    · rcases hz with hz | ⟨c', t', z', hz⟩
                      · simp at hz
                      · rw [List.cons_append, List.cons.injEq] at hz
                        exact Or.inr ⟨c', t', z, by rw [hz.1]⟩
                  obtain ⟨i1, i2⟩ := ih hz'
                  rcases o with _ | t
                  · have hzne : z ≠ [] := by
                      rintro rfl
                      rcases hz with hz | ⟨c', t', z', hz⟩
                      · simp at hz
                      · simp at hz
                    obtain ⟨acc, b, hab⟩ : ∃ acc b, blocks z = acc ++ [b] := by
                      exact ⟨_, _, (List.dropLast_append_getLast (i2 hzne)).symm⟩
                    obtain ⟨g, u, r⟩ := b
                    rw [hstep, hab, hstpN]
                    refine ⟨?_, fun _ => by simp⟩
                    conv_lhs => rw [i1, hab]
                    rw [hfl, hfl]
                    simp
                  · rw [hstep, hstpS]
                    refine ⟨?_, fun _ => by simp⟩
                    conv_lhs => rw [i1]
                    rw [hfl, hfl]
                    simp
              refine (key y ?_).1
              rcases y with _ | ⟨⟨c, o⟩, y⟩
              · exact Or.inl rfl
              · rcases o with _ | t
                · exfalso
                  have h3 := hv.2.2 0 (by simp) (by simp)
                  obtain ⟨t, ht⟩ := hne c
                  have h4 := h3 ht
                  simp [held, heldToks] at h4
                · exact Or.inr ⟨c, t, y, rfl⟩
            subst hd
            have hlen : (desc y).length = (blocks y).length := by simp [desc]
            have hg : ∀ j : Fin (desc y).length, (desc y).get j =
                (((blocks y).get (Fin.cast hlen j)).2.1, ((blocks y).get (Fin.cast hlen j)).2.2.length) := by
              have hgen : ∀ (zs : List (T × ℕ)) (f : C × T × List C → T × ℕ)
                  (_ : zs = (blocks y).map f) (j : Fin zs.length) (h : j.1 < (blocks y).length),
                  zs.get j = f ((blocks y).get ⟨j.1, h⟩) := by
                intro zs f hz j h
                subst hz
                simp
              intro j
              exact hgen (desc y) (fun b => (b.2.1, b.2.2.length)) rfl j (hlen ▸ j.2)
            have hn : ∀ j : Fin (desc y).length,
                ((desc y).get j).2 = ((blocks y).get (Fin.cast hlen j)).2.2.length := by
              intro j; rw [hg]
            refine ⟨fun j => ((blocks y).get (Fin.cast hlen j)).1,
              fun j m => ((blocks y).get (Fin.cast hlen j)).2.2.get (Fin.cast (hn j) m), ?_⟩
            rw [hYfl]
            refine hfirst.trans (congrArg fl ?_)
            refine List.ext_get (by simp [hlen]) ?_
            intro i hi1 hi2
            rw [List.get_ofFn]
            have hi3 : i < (desc y).length := by rw [hlen]; exact hi1
            have hlist : ∀ (r : List C) (n : ℕ) (hnr : n = r.length),
                List.ofFn (fun m : Fin n => r.get (Fin.cast hnr m)) = r := by
              intro r n hnr
              subst hnr
              exact List.ofFn_get r
            have e1 := hlist ((blocks y).get ⟨i, hi1⟩).2.2 _ (hn ⟨i, hi3⟩)
            have e2 : ((desc y).get ⟨i, hi3⟩).1 = ((blocks y).get ⟨i, hi1⟩).2.1 :=
              congrArg Prod.fst (hg ⟨i, hi3⟩)
            exact Prod.ext rfl (Prod.ext e2.symm e1.symm)
          · intro x cs l
            have h1 : ∀ bs, heldToks (fl bs) = bs.map (fun b => b.2.1) := by
              intro bs
              rw [hfl]
              induction bs with
              | nil => rfl
              | cons b bs ih =>
                have h0 : ∀ r : List C,
                    (r.map (fun c => ((c, none) : C × Option T))).filterMap Prod.snd = [] := by
                  intro r
                  induction r with
                  | nil => rfl
                  | cons a r ihr => rw [List.map_cons, List.filterMap_cons_none rfl, ihr]
                unfold heldToks at ih ⊢
                rw [List.flatMap_cons, List.filterMap_append, List.filterMap_cons_some (f := Prod.snd) (b := b.2.1) rfl, h0, ih]
                rfl
            rw [hYfl, h1, List.map_ofFn]
            unfold toks
            refine Eq.trans ?_ (congrArg (List.map Prod.fst) (List.ofFn_get x))
            rw [List.map_ofFn]
            rfl
          · intro x cs l
            have h1 : ∀ bs, (fl bs).length = bs.length + (bs.map (fun b => b.2.2.length)).sum := by
              intro bs
              rw [hfl]
              induction bs with
              | nil => rfl
              | cons b bs ih =>
                rw [List.flatMap_cons, List.length_append, ih]
                simp only [List.length_cons, List.length_map, List.map_cons, List.sum_cons]
                omega
            rw [hYfl, h1, List.map_ofFn]
            unfold phi
            have h2 : x.map Prod.snd = List.ofFn (fun j => (x.get j).2) := by
              refine Eq.trans (congrArg (List.map Prod.snd) (List.ofFn_get x).symm) ?_
              rw [List.map_ofFn]
              rfl
            rw [h2, List.length_ofFn]
            congr 2
            congr 1
            funext j
            simp
        have L0b : ∀ (Y : (x : List (T × ℕ)) → (Fin x.length → C) → ((j : Fin x.length) → Fin (x.get j).2 → C) → CState C T)
          (hY : ∀ x cs l, Y x cs l = (List.finRange x.length).flatMap (fun j =>
            (cs j, some (x.get j).1) :: List.ofFn (fun m => (l j m, none))))
          (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (sk : CState C T → List (Option (C × Option T)))
          (hsk : ∀ y, sk y = y.map (fun e => if e.2 = none then none else some e))
          (wd : CState C T → List (Option C × Option T))
          (hwd : ∀ y, wd y = y.map (fun e => (if e.2 = none then some e.1 else none, e.2))),
          (∀ x cs l, (x.map Prod.fst).Nodup → (Valid P (Y x cs l) ↔ (∀ j, (x.get j).1 ∈ P.tok (cs j)) ∧
            ∀ j m, P.tok (l j m) ⊆ ((toks x).take (j + 1)).toFinset)) ∧
          (∀ x cs l (z : C → ℂ), ∏ c, z c ^ Mtot (Y x cs l) c = (∏ j, z (cs j)) * ∏ j, ∏ m, z (l j m)) ∧
          (∀ x cs l, lamIn (Y x cs l) = ∏ j, ∏ m, P.lam (l j m)) ∧
          (∀ x cs l l', sk (Y x cs l) = sk (Y x cs l')) ∧
          (∀ x cs l, (∏ q ∈ range (Y x cs l).length, (kfun P (heldToks ((Y x cs l).take (q + 1))))⁻¹)
            = ∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ ((x.get j).2 + 1)) ∧
          (∀ x cs cs' l, wd (Y x cs l) = wd (Y x cs' l)) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          clear hk
          clear h2
          clear h1
          intro Y hY lamIn hlamIn sk hsk wd hwd
          have hPr : ∀ {M : Type} [CommMonoid M] (p : T × ℕ) (x : List (T × ℕ)) (f : Fin (p :: x).length → M),
              ∏ j, f j = f ⟨0, Nat.succ_pos _⟩ * ∏ j : Fin x.length, f j.succ := by
            intro M _ p x f
            exact Fin.prod_univ_succ (n := x.length) f
          have hAl : ∀ (p : T × ℕ) (x : List (T × ℕ)) (f : Fin (p :: x).length → Prop),
              (∀ j, f j) ↔ f ⟨0, Nat.succ_pos _⟩ ∧ ∀ j : Fin x.length, f j.succ := by
            intro p x f
            exact Fin.forall_fin_succ (n := x.length)
          have hcons : ∀ (p : T × ℕ) (x : List (T × ℕ)) (cs : Fin (p :: x).length → C)
              (l : (j : Fin (p :: x).length) → Fin ((p :: x).get j).2 → C),
              Y (p :: x) cs l = (cs ⟨0, Nat.succ_pos _⟩, some p.1) ::
                ((List.ofFn (n := p.2) (l ⟨0, Nat.succ_pos _⟩)).map (fun c => ((c, none) : C × Option T)) ++
                  Y x (fun j => cs j.succ) (fun j => l j.succ)) := by
            intro p x cs l
            rw [hY, hY, List.map_ofFn]
            have h1 : List.finRange (p :: x).length
                = (⟨0, Nat.succ_pos _⟩ : Fin (p :: x).length) :: (List.finRange x.length).map Fin.succ :=
              List.finRange_succ
            rw [h1, List.flatMap_cons, List.flatMap_map]
            rfl
          have hnil : ∀ cs l, Y [] cs l = [] := by
            intro cs l
            rw [hY]
            rfl
          -- generic product of a map over the state
          have hmapprod : ∀ {M : Type} [CommMonoid M] (g : C × Option T → M) x cs l,
              ((Y x cs l).map g).prod = (∏ j, g (cs j, some (x.get j).1)) * ∏ j, ∏ m, g (l j m, none) := by
            intro M _ g x
            induction x with
            | nil =>
              intro cs l
              rw [hnil]
              simp
            | cons p x ih =>
              intro cs l
              rw [hcons, hPr, hPr, List.map_cons, List.prod_cons, List.map_append, List.prod_append, ih,
                List.map_map, List.map_ofFn, List.prod_ofFn]
              simp only [Function.comp]
              rw [← mul_assoc, mul_mul_mul_comm]
              rfl
          have hhA : ∀ a b : CState C T, heldToks (a ++ b) = heldToks a ++ heldToks b := by
            intro a b
            exact List.filterMap_append
          have hhS : ∀ (c : C) (t : T), heldToks [(c, some t)] = [t] := by intro c t; rfl
          have hhN : ∀ (L : List C), heldToks (L.map (fun c => ((c, none) : C × Option T))) = [] := by
            intro L
            induction L with
            | nil => rfl
            | cons c L ih => exact ih
          have hV : ∀ (a : CState C T) (e : C × Option T), Valid P (a ++ [e]) ↔ Valid P a ∧
              (e.2 = none → P.tok e.1 ⊆ (heldToks a).toFinset) ∧
              ∀ t, e.2 = some t → t ∈ P.tok e.1 ∧ t ∉ heldToks a := by
            intro a e
            have hget1 : ∀ i (h : i < a.length) (h' : i < (a ++ [e]).length), (a ++ [e])[i]'h' = a[i]'h :=
              fun i h h' => List.getElem_append_left h
            have hget2 : ∀ (h' : a.length < (a ++ [e]).length), (a ++ [e])[a.length]'h' = e := by
              intro h'
              simp
            have htk : ∀ i, i ≤ a.length → (a ++ [e]).take i = a.take i :=
              fun i h => List.take_append_of_le_length h
            have hlen : (a ++ [e]).length = a.length + 1 := by simp
            have hnd : (heldToks (a ++ [e])).Nodup ↔ (heldToks a).Nodup ∧ ∀ t, e.2 = some t → t ∉ heldToks a := by
              rw [hhA]
              obtain ⟨c, o⟩ := e
              cases o with
              | none =>
                have : heldToks [((c, none) : C × Option T)] = [] := rfl
                rw [this, List.append_nil]
                constructor
                · intro h
                  exact ⟨h, fun t ht => by cases ht⟩
                · intro h
                  exact h.1
              | some u =>
                rw [hhS, List.nodup_append]
                constructor
                · intro h
                  refine ⟨h.1, fun t ht => ?_⟩
                  cases ht
                  intro hm
                  exact h.2.2 u hm u (List.mem_singleton.2 rfl) rfl
                · intro h
                  refine ⟨h.1, List.nodup_singleton u, ?_⟩
                  intro v hv w hw hvw
                  rw [List.mem_singleton] at hw
                  subst hw
                  subst hvw
                  exact h.2 v rfl hv
            constructor
            · rintro ⟨h1, h2, h3⟩
              have h1' := hnd.1 h1
              refine ⟨⟨h1'.1, ?_, ?_⟩, ?_, ?_⟩
              · intro i h t ht
                have := h2 i (by omega) t
                rw [hget1 i h] at this
                exact this ht
              · intro i h hn
                have := h3 i (by omega)
                rw [hget1 i h, htk i h.le] at this
                exact this hn
              · intro hn
                have := h3 a.length (by omega)
                rw [hget2, htk _ le_rfl, List.take_length] at this
                exact this hn
              · intro t ht
                have := h2 a.length (by omega) t
                rw [hget2] at this
                exact ⟨this ht, h1'.2 t ht⟩
            · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
              refine ⟨hnd.2 ⟨h1, fun t ht => (h5 t ht).2⟩, ?_, ?_⟩
              · intro i h t
                by_cases hi : i < a.length
                · rw [hget1 i hi]
                  exact h2 i hi t
                · have hi' : i = a.length := by omega
                  subst hi'
                  rw [hget2]
                  exact fun ht => (h5 t ht).1
              · intro i h
                by_cases hi : i < a.length
                · rw [hget1 i hi, htk i hi.le]
                  exact h3 i hi
                · have hi' : i = a.length := by omega
                  subst hi'
                  rw [hget2, htk _ le_rfl, List.take_length]
                  exact h4
          have hVN : ∀ (L : List C) (a : CState C T),
              Valid P (a ++ L.map (fun c => ((c, none) : C × Option T))) ↔ Valid P a ∧
                ∀ c ∈ L, P.tok c ⊆ (heldToks a).toFinset := by
            intro L
            induction L with
            | nil =>
              intro a
              simp
            | cons c L ih =>
              intro a
              have e1 : a ++ (c :: L).map (fun c => ((c, none) : C × Option T))
                  = (a ++ [(c, none)]) ++ L.map (fun c => ((c, none) : C × Option T)) := by simp
              have e2 : heldToks (a ++ [((c, none) : C × Option T)]) = heldToks a := by
                rw [hhA]
                exact List.append_nil _
              rw [e1, ih, hV, e2, List.forall_mem_cons]
              constructor
              · rintro ⟨⟨h1, h2, _⟩, h4⟩
                exact ⟨h1, h2 rfl, h4⟩
              · rintro ⟨h1, h2, h4⟩
                exact ⟨⟨h1, fun _ => h2, fun t ht => by cases ht⟩, h4⟩
          have hsplit : ∀ (a : CState C T) (e : C × Option T) (b c : CState C T),
              a ++ e :: (b ++ c) = ((a ++ [e]) ++ b) ++ c := by
            intro a e b c
            simp
          have hheld : ∀ (a : CState C T) (c : C) (t : T) (L : List C),
              heldToks ((a ++ [(c, some t)]) ++ L.map (fun c => ((c, none) : C × Option T)))
                = heldToks a ++ [t] := by
            intro a c t L
            rw [hhA, hhA, hhN, hhS, List.append_nil]
          have hVY : ∀ (x : List (T × ℕ)) (a : CState C T) cs l, (heldToks a ++ toks x).Nodup →
              (Valid P (a ++ Y x cs l) ↔ Valid P a ∧ (∀ j, (x.get j).1 ∈ P.tok (cs j)) ∧
                ∀ j m, P.tok (l j m) ⊆ (heldToks a ++ (toks x).take (j + 1)).toFinset) := by
            intro x
            induction x with
            | nil =>
              intro a cs l _
              rw [hnil, List.append_nil]
              exact ⟨fun h => ⟨h, fun j => j.elim0, fun j => j.elim0⟩, fun h => h.1⟩
            | cons p x ih =>
              intro a cs l hnd
              have hnd' : ((heldToks a ++ [p.1]) ++ toks x).Nodup := by
                have : heldToks a ++ toks (p :: x) = (heldToks a ++ [p.1]) ++ toks x := by
                  simp [toks]
                rw [← this]
                exact hnd
              have hp : p.1 ∉ heldToks a := by
                intro hm
                have h1 := (List.nodup_append.1 (List.nodup_append.1 hnd').1).2.2
                exact h1 p.1 hm p.1 (List.mem_singleton.2 rfl) rfl
              rw [hcons, hsplit, ih _ _ _ (by rw [hheld]; exact hnd'), hheld, hVN, hV, hhA, hhS, hAl, hAl,
                List.forall_mem_ofFn_iff]
              have htk : ∀ n : ℕ, heldToks a ++ [p.1] ++ (toks x).take (n + 1)
                  = heldToks a ++ (toks (p :: x)).take (n + 1 + 1) := by
                intro n
                simp [toks]
              have htk0 : heldToks a ++ [p.1] = heldToks a ++ (toks (p :: x)).take (0 + 1) := by
                simp [toks]
              constructor
              · rintro ⟨⟨⟨h1, _, h3⟩, h4⟩, h5, h6⟩
                refine ⟨h1, ⟨(h3 p.1 rfl).1, h5⟩, ?_, ?_⟩
                · intro m
                  have := h4 m
                  rw [htk0] at this
                  exact this
                · intro j m
                  have := h6 j m
                  rw [htk] at this
                  exact this
              · rintro ⟨h1, ⟨h3, h5⟩, h4, h6⟩
                refine ⟨⟨⟨h1, (fun h => absurd h (Option.some_ne_none _)), ?_⟩, ?_⟩, h5, ?_⟩
                · intro t ht
                  cases ht
                  exact ⟨h3, hp⟩
                · intro m
                  rw [htk0]
                  exact h4 m
                · intro j m
                  rw [htk]
                  exact h6 j m
          have hK : ∀ (F : List T → ℝ) (a : CState C T) (e : C × Option T),
              (∏ q ∈ range (a ++ [e]).length, F (heldToks ((a ++ [e]).take (q + 1))))
                = (∏ q ∈ range a.length, F (heldToks (a.take (q + 1)))) * F (heldToks (a ++ [e])) := by
            intro F a e
            have hlen : (a ++ [e]).length = a.length + 1 := by simp
            rw [hlen, Finset.prod_range_succ]
            congr 1
            · refine Finset.prod_congr rfl (fun q hq => ?_)
              rw [List.take_append_of_le_length (Finset.mem_range.1 hq)]
            · rw [List.take_of_length_le hlen.le]
          have hKN : ∀ (F : List T → ℝ) (L : List C) (a : CState C T),
              (∏ q ∈ range (a ++ L.map (fun c => ((c, none) : C × Option T))).length,
                F (heldToks ((a ++ L.map (fun c => ((c, none) : C × Option T))).take (q + 1))))
                = (∏ q ∈ range a.length, F (heldToks (a.take (q + 1)))) * F (heldToks a) ^ L.length := by
            intro F L
            induction L with
            | nil =>
              intro a
              simp
            | cons c L ih =>
              intro a
              have e1 : a ++ (c :: L).map (fun c => ((c, none) : C × Option T))
                  = (a ++ [(c, none)]) ++ L.map (fun c => ((c, none) : C × Option T)) := by simp
              have e2 : heldToks (a ++ [((c, none) : C × Option T)]) = heldToks a := by
                rw [hhA]
                exact List.append_nil _
              rw [e1, ih, hK, e2, List.length_cons, pow_succ']
              ring
          have hKY : ∀ (F : List T → ℝ) (x : List (T × ℕ)) (a : CState C T) cs l,
              (∏ q ∈ range (a ++ Y x cs l).length, F (heldToks ((a ++ Y x cs l).take (q + 1))))
                = (∏ q ∈ range a.length, F (heldToks (a.take (q + 1)))) *
                  ∏ j : Fin x.length, F (heldToks a ++ (toks x).take (j + 1)) ^ ((x.get j).2 + 1) := by
            intro F x
            induction x with
            | nil =>
              intro a cs l
              rw [hnil, List.append_nil]
              simp
            | cons p x ih =>
              intro a cs l
              have htk : ∀ n : ℕ, heldToks a ++ [p.1] ++ (toks x).take (n + 1)
                  = heldToks a ++ (toks (p :: x)).take (n + 1 + 1) := by
                intro n
                simp [toks]
              have htk0 : heldToks a ++ [p.1] = heldToks a ++ (toks (p :: x)).take (0 + 1) := by
                simp [toks]
              rw [hcons, hsplit, ih, hheld, hKN, hK, hhA, hhS, hPr, List.length_ofFn, mul_assoc, mul_assoc,
                ← mul_assoc (F _) (F _ ^ _), ← pow_succ']
              simp only [htk]
              rw [htk0]
              rfl
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x cs l hnd
            have h := hVY x [] cs l hnd
            have h0 : Valid P ([] : CState C T) :=
              ⟨List.nodup_nil, fun i h => absurd h (Nat.not_lt_zero i), fun i h => absurd h (Nat.not_lt_zero i)⟩
            exact ⟨fun hv => (h.1 hv).2, fun hv => h.2 ⟨h0, hv⟩⟩
          · intro x cs l z
            have hM : ∀ y : CState C T, ∏ c, z c ^ Mtot y c = (y.map (fun e => z e.1)).prod := by
              intro y
              induction y with
              | nil => simp [Mtot]
              | cons e y ih =>
                have hm : ∀ c, Mtot (e :: y) c = (if e.1 = c then 1 else 0) + Mtot y c := by
                  intro c
                  unfold Mtot
                  by_cases hc : e.1 = c
                  · rw [List.filter_cons_of_pos (by simpa using hc), if_pos hc, List.length_cons, add_comm]
                  · rw [List.filter_cons_of_neg (by simpa using hc), if_neg hc, zero_add]
                rw [List.map_cons, List.prod_cons, ← ih]
                simp only [hm, pow_add]
                rw [Finset.prod_mul_distrib]
                congr 1
                simp [pow_ite, Finset.prod_ite_eq]
            rw [hM, hmapprod (fun e => z e.1)]
          · intro x cs l
            rw [hlamIn, hmapprod (fun e => if e.2 = none then P.lam e.1 else 1)]
            simp only [reduceCtorEq, if_false, if_true, Finset.prod_const_one, one_mul]
          · intro x
            induction x with
            | nil =>
              intro cs l l'
              rw [hnil, hnil]
            | cons p x ih =>
              intro cs l l'
              have ih' := ih (fun j => cs j.succ) (fun j => l j.succ) (fun j => l' j.succ)
              rw [hsk, hsk] at ih'
              rw [hsk, hsk, hcons, hcons, List.map_cons, List.map_cons, List.map_append, List.map_append,
                List.map_map, List.map_map, ih', List.map_ofFn, List.map_ofFn]
              rfl
          · intro x cs l
            exact (hKY (fun L => (kfun P L)⁻¹) x [] cs l).trans (by
              simp only [List.length_nil, Finset.range_zero, Finset.prod_empty, one_mul]
              rfl)
          · intro x
            induction x with
            | nil =>
              intro cs cs' l
              rw [hnil, hnil]
            | cons p x ih =>
              intro cs cs' l
              have ih' := ih (fun j => cs j.succ) (fun j => cs' j.succ) (fun j => l j.succ)
              rw [hwd, hwd] at ih'
              rw [hwd, hwd, hcons, hcons, List.map_cons, List.map_cons, List.map_append, List.map_append, ih']
              rfl
        have L9 : ∀ (Y : (x : List (T × ℕ)) → (Fin x.length → C) → ((j : Fin x.length) → Fin (x.get j).2 → C) → CState C T)
          (hY : ∀ x cs l, Y x cs l = (List.finRange x.length).flatMap (fun j =>
            (cs j, some (x.get j).1) :: List.ofFn (fun m => (l j m, none))))
          (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (Pi : CState C T → ℝ)
          (hPi : ∀ y, Pi y = piLam P (heldToks y) * lamIn y *
            (∏ q ∈ range y.length, (kfun P (heldToks (y.take (q + 1))))⁻¹) *
            ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹)
          (sk : CState C T → List (Option (C × Option T)))
          (hsk : ∀ y, sk y = y.map (fun e => if e.2 = none then none else some e))
          (wd : CState C T → List (Option C × Option T))
          (hwd : ∀ y, wd y = y.map (fun e => (if e.2 = none then some e.1 else none, e.2)))
          (hYb : ∀ x cs l, blocks (Y x cs l) = List.ofFn (fun j => (cs j, (x.get j).1, List.ofFn (l j))))
          (hYd : ∀ x cs l, desc (Y x cs l) = x)
          (hYh : ∀ x cs l, holderTypes (Y x cs l) = List.ofFn cs)
          (hYi : ∀ x cs l cs' l', Y x cs l = Y x cs' l' → cs = cs' ∧ l = l')
          (hYs : ∀ x y, Valid P y → desc y = x → ∃ cs l, y = Y x cs l)
          (hYt : ∀ x cs l, heldToks (Y x cs l) = toks x)
          (hYl : ∀ x cs l, (Y x cs l).length = phi x)
          (hYv : ∀ x cs l, (x.map Prod.fst).Nodup → (Valid P (Y x cs l) ↔ (∀ j, (x.get j).1 ∈ P.tok (cs j)) ∧
            ∀ j m, P.tok (l j m) ⊆ ((toks x).take (j + 1)).toFinset))
          (hYm : ∀ x cs l (z : C → ℂ), ∏ c, z c ^ Mtot (Y x cs l) c = (∏ j, z (cs j)) * ∏ j, ∏ m, z (l j m))
          (hYlam : ∀ x cs l, lamIn (Y x cs l) = ∏ j, ∏ m, P.lam (l j m))
          (hYsk : ∀ x cs l l', sk (Y x cs l) = sk (Y x cs l'))
          (hYk : ∀ x cs l, (∏ q ∈ range (Y x cs l).length, (kfun P (heldToks ((Y x cs l).take (q + 1))))⁻¹)
            = ∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ ((x.get j).2 + 1))
          (hYw : ∀ x cs cs' l, wd (Y x cs l) = wd (Y x cs' l))
          (Q : CState C T → ℝ)
          (hQ0 : ∀ y, 0 ≤ Q y)
          (hQv : ∀ y, ¬ Valid P y → Q y = 0)
          (k : ℝ)
          (hk0 : 0 ≤ k)
          (ih : ∀ y (F : Finset (CState C T)), (∀ y1 ∈ F, wd y1 = wd y) → ∑ y1 ∈ F, Q y1 ≤ k * Pi y),
          ∀ x : State T, prob Q (fun y => desc y = x.1) ≤ k * weight P x := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          clear hstab
          intro Y hY lamIn hlamIn Pi hPi sk hsk wd hwd hYb hYd hYh hYi hYs hYt hYl hYv hYm hYlam hYsk hYk hYw Q hQ0 hQv k hk0 ih
          rintro ⟨x, hx⟩
          obtain ⟨hlam, -, has, -, -, hs, heta⟩ := hS
          have hkf : ∀ l : List T, 0 ≤ kfun P l := fun l => Finset.sum_nonneg (fun _ _ => hs _)
          have hlt : ∀ S t, 0 ≤ lamTok P S t := fun S t =>
            Finset.sum_nonneg (fun c _ => mul_nonneg (hlam c).le (has c S t))
          have hpl : ∀ l : List T, 0 ≤ piLam P l := fun l => Finset.prod_nonneg (fun _ _ => hlt _ _)
          obtain ⟨K, hK⟩ : ∃ K : ℝ, K = piLam P (toks x) *
              (∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ ((x.get j).2 + 1)) *
              ∏ q ∈ range (phi x), (P.eta (q + 1))⁻¹ := ⟨_, rfl⟩
          have hK0 : 0 ≤ K := by
            rw [hK]
            refine mul_nonneg (mul_nonneg (hpl _) (Finset.prod_nonneg fun j _ => ?_))
              (Finset.prod_nonneg fun q _ => ?_)
            · exact pow_nonneg (inv_nonneg.mpr (hkf _)) _
            · exact inv_nonneg.mpr (heta (q + 1) (by omega)).le
          obtain ⟨f, hf⟩ : ∃ f : Fin x.length → C → ℝ, ∀ j c, f j c =
              if P.tok c ⊆ ((toks x).take (j + 1)).toFinset then P.lam c else 0 := ⟨_, fun _ _ => rfl⟩
          have hf0 : ∀ j c, 0 ≤ f j c := by
            intro j c
            rw [hf]
            split_ifs
            · exact (hlam c).le
            · exact le_rfl
          have hPiY : ∀ cs l, Pi (Y x cs l) = K * ∏ j, ∏ m, P.lam (l j m) := by
            intro cs l
            rw [hPi, hYt, hYlam, hYk, hYl, hK]
            ring
          -- fixed inactive types
          have hl : ∀ l : (j : Fin x.length) → Fin (x.get j).2 → C,
              ∑ cs, Q (Y x cs l) ≤ k * K * ∏ j, ∏ m, f j (l j m) := by
            intro l
            have hR : 0 ≤ k * K * ∏ j, ∏ m, f j (l j m) :=
              mul_nonneg (mul_nonneg hk0 hK0)
                (Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun m _ => hf0 _ _)
            by_cases hg : ∀ j m, P.tok (l j m) ⊆ ((toks x).take (j + 1)).toFinset
            · rcases isEmpty_or_nonempty (Fin x.length → C) with he | ⟨⟨cs0⟩⟩
              · rw [Finset.univ_eq_empty, Finset.sum_empty]
                exact hR
              · have h := ih (Y x cs0 l) (Finset.univ.image (fun cs => Y x cs l)) (by
                  intro y1 hy1
                  rw [Finset.mem_image] at hy1
                  obtain ⟨cs, -, rfl⟩ := hy1
                  exact hYw x cs cs0 l)
                rw [Finset.sum_image (fun a _ b _ hab => (hYi x a l b l hab).1), hPiY] at h
                have hprod : ∏ j, ∏ m, f j (l j m) = ∏ j, ∏ m, P.lam (l j m) :=
                  Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun m _ => by
                    rw [hf, if_pos (hg j m)]
                rw [hprod, mul_assoc]
                exact h
            · have hz : ∑ cs, Q (Y x cs l) = 0 :=
                Finset.sum_eq_zero fun cs _ => hQv _ fun hv => hg ((hYv x cs l hx).1 hv).2
              rw [hz]
              exact hR
          -- the probability as a finite sum
          have hprob : prob Q (fun y => desc y = x) = ∑ l, ∑ cs, Q (Y x cs l) := by
            unfold prob
            rw [tsum_eq_sum (s := Finset.univ.image
              (fun p : ((j : Fin x.length) → Fin (x.get j).2 → C) × (Fin x.length → C) => Y x p.2 p.1))]
            · rw [Finset.sum_image (fun a _ b _ hab => by
                obtain ⟨h1', h2'⟩ := hYi x a.2 a.1 b.2 b.1 hab
                exact Prod.ext h2' h1'), Fintype.sum_prod_type]
              refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun cs _ => ?_
              exact Set.indicator_of_mem (s := {y | desc y = x}) (hYd x cs l) Q
            · intro y hy
              by_cases hd : desc y = x
              · rw [Set.indicator_of_mem (s := {y | desc y = x}) hd]
                refine hQv y fun hv => hy ?_
                obtain ⟨cs, l, rfl⟩ := hYs x y hv hd
                exact Finset.mem_image.mpr ⟨(l, cs), Finset.mem_univ _, rfl⟩
              · exact Set.indicator_of_notMem (s := {y | desc y = x}) hd Q
          -- the sum over the inactive types
          have hsum : ∑ l : (j : Fin x.length) → Fin (x.get j).2 → C, ∏ j, ∏ m, f j (l j m) =
              ∏ j : Fin x.length, (lamU P ((toks x).take (j + 1)).toFinset) ^ (x.get j).2 := by
            have hc : ∀ j : Fin x.length, ∑ c, f j c = lamU P ((toks x).take (j + 1)).toFinset := by
              intro j
              unfold lamU
              rw [Finset.sum_filter]
              exact Finset.sum_congr rfl fun c _ => hf j c
            have hin : ∀ j : Fin x.length, (∑ c, f j c) ^ (x.get j).2 =
                ∑ g : Fin (x.get j).2 → C, ∏ m, f j (g m) := by
              intro j
              have h := Finset.prod_univ_sum (fun _ : Fin (x.get j).2 => (Finset.univ : Finset C))
                (fun _ c => f j c)
              rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
              exact h
            have hout := Finset.prod_univ_sum
              (fun j : Fin x.length => (Finset.univ : Finset (Fin (x.get j).2 → C)))
              (fun j g => ∏ m, f j (g m))
            rw [Fintype.piFinset_univ] at hout
            rw [← hout]
            exact Finset.prod_congr rfl fun j _ => by rw [← hin, hc]
          have hlen : (toks x).length = x.length := by
            unfold toks
            exact List.length_map _
          have hpiK : piK P (toks x) = ∏ j : Fin x.length, kfun P ((toks x).take (j + 1)) := by
            unfold piK
            rw [← Finset.prod_range (fun j => kfun P ((toks x).take (j + 1))),
              ← Finset.prod_range (fun j => kfun P ((toks x).take (j + 1))), hlen]
          have hIcc : ∏ j ∈ Icc 1 (phi x), (P.eta j)⁻¹ = ∏ q ∈ range (phi x), (P.eta (q + 1))⁻¹ := by
            symm
            refine Finset.prod_bij (fun q _ => q + 1) ?_ ?_ ?_ ?_
            · intro q hq
              rw [Finset.mem_range] at hq
              rw [Finset.mem_Icc]
              omega
            · intro a _ b _ hab
              exact Nat.succ_injective hab
            · intro b hb
              rw [Finset.mem_Icc] at hb
              exact ⟨b - 1, by rw [Finset.mem_range]; omega, by omega⟩
            · intro q _
              rfl
          have hw : K * ∏ j : Fin x.length, (lamU P ((toks x).take (j + 1)).toFinset) ^ (x.get j).2 =
              weightL P x := by
            unfold weightL alpha
            rw [hIcc, hpiK, hK, div_eq_mul_inv, ← Finset.prod_inv_distrib]
            have e1 : ∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ ((x.get j).2 + 1) =
                (∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ (x.get j).2) *
                ∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ := by
              rw [← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun j _ => pow_succ _ _
            have e2 : ∏ j : Fin x.length, (lamU P ((toks x).take (j + 1)).toFinset /
                  kfun P ((toks x).take (j + 1))) ^ (x.get j).2 =
                (∏ j : Fin x.length, (lamU P ((toks x).take (j + 1)).toFinset) ^ (x.get j).2) *
                ∏ j : Fin x.length, (kfun P ((toks x).take (j + 1)))⁻¹ ^ (x.get j).2 := by
              rw [← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun j _ => by rw [div_eq_mul_inv, mul_pow]
            rw [e1, e2]
            ring
          change prob Q (fun y => desc y = x) ≤ k * weightL P x
          rw [hprob, ← hw, ← hsum, ← mul_assoc, Finset.mul_sum]
          exact Finset.sum_le_sum fun l _ => hl l
        have L11 : ∀ (Y : (x : List (T × ℕ)) → (Fin x.length → C) → ((j : Fin x.length) → Fin (x.get j).2 → C) → CState C T)
          (hY : ∀ x cs l, Y x cs l = (List.finRange x.length).flatMap (fun j =>
            (cs j, some (x.get j).1) :: List.ofFn (fun m => (l j m, none))))
          (lamIn : CState C T → ℝ)
          (hlamIn : ∀ y, lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod)
          (sk : CState C T → List (Option (C × Option T)))
          (hsk : ∀ y, sk y = y.map (fun e => if e.2 = none then none else some e))
          (hYb : ∀ x cs l, blocks (Y x cs l) = List.ofFn (fun j => (cs j, (x.get j).1, List.ofFn (l j))))
          (hYd : ∀ x cs l, desc (Y x cs l) = x)
          (hYh : ∀ x cs l, holderTypes (Y x cs l) = List.ofFn cs)
          (hYi : ∀ x cs l cs' l', Y x cs l = Y x cs' l' → cs = cs' ∧ l = l')
          (hYs : ∀ x y, Valid P y → desc y = x → ∃ cs l, y = Y x cs l)
          (hYt : ∀ x cs l, heldToks (Y x cs l) = toks x)
          (hYl : ∀ x cs l, (Y x cs l).length = phi x)
          (hYv : ∀ x cs l, (x.map Prod.fst).Nodup → (Valid P (Y x cs l) ↔ (∀ j, (x.get j).1 ∈ P.tok (cs j)) ∧
            ∀ j m, P.tok (l j m) ⊆ ((toks x).take (j + 1)).toFinset))
          (hYm : ∀ x cs l (z : C → ℂ), ∏ c, z c ^ Mtot (Y x cs l) c = (∏ j, z (cs j)) * ∏ j, ∏ m, z (l j m))
          (hYlam : ∀ x cs l, lamIn (Y x cs l) = ∏ j, ∏ m, P.lam (l j m))
          (hYsk : ∀ x cs l l', sk (Y x cs l) = sk (Y x cs l'))
          (Q : CState C T → ℝ)
          (hQ0 : ∀ y, 0 ≤ Q y)
          (hQ1 : HasSum Q 1)
          (hQv : ∀ y, ¬ Valid P y → Q y = 0)
          (hinv : ∀ y y', Valid P y → Valid P y' → sk y = sk y' → Q y * lamIn y' = Q y' * lamIn y)
          (hdesc : ∀ x : State T, prob Q (fun y => desc y = x.1) = piZero P * weight P x)
          (z : C → ℂ)
          (hz : ∀ c, ‖z c‖ < 1),
          HasSum (fun x : State T => (commonFactor P x.1 : ℂ) *
              (∑ cs : Fin x.1.length → C, (Gcond Q x.1 (List.ofFn cs) : ℂ) * ∏ j, z (cs j)) *
              ∏ j : Fin x.1.length,
                ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
                  ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2)
            (∑' y, (Q y : ℂ) * ∏ c, z c ^ Mtot y c) := by
          as_aux_lemma =>
          clear hz
          clear z
          clear hQ
          clear Q
          intro Y hY lamIn hlamIn sk hsk hYb hYd hYh hYi hYs hYt hYl hYv hYm hYlam hYsk Q hQ0 hQ1 hQv hinv hdesc z hz
          classical
          have hlam : ∀ c, 0 < P.lam c := hS.1
          -- generic expansion
          have hexp : ∀ (R : Type) [CommSemiring R] (k : ℕ) (n : Fin k → ℕ) (f : Fin k → C → R),
              ∑ l : ((j : Fin k) → Fin (n j) → C), ∏ j, ∏ m, f j (l j m) = ∏ j, (∑ c, f j c) ^ (n j) := by
            intro R _ k n f
            have h1 : ∀ j, (∑ c, f j c) ^ (n j) = ∑ p : Fin (n j) → C, ∏ m, f j (p m) := by
              intro j
              exact Fintype.sum_pow (f j) (n j)
            rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_univ_sum, Fintype.piFinset_univ]
          -- skeleton factorisation
          have hfac : ∀ x : State T, ∀ cs, ∃ H : ℝ, ∀ l, Q (Y x.1 cs l) = H * ∏ j, ∏ m,
              (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset then P.lam (l j m) else 0) := by
            intro x cs
            by_cases hex : ∃ l0, Valid P (Y x.1 cs l0)
            · obtain ⟨l0, hl0⟩ := hex
              refine ⟨Q (Y x.1 cs l0) / lamIn (Y x.1 cs l0), fun l => ?_⟩
              have hpos : ∀ l, 0 < lamIn (Y x.1 cs l) := by
                intro l
                rw [hYlam]
                exact Finset.prod_pos fun j _ => Finset.prod_pos fun m _ => hlam _
              by_cases hl : Valid P (Y x.1 cs l)
              · have hg := ((hYv x.1 cs l x.2).1 hl).2
                have e : (∏ j, ∏ m, (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                    then P.lam (l j m) else 0)) = lamIn (Y x.1 cs l) := by
                  rw [hYlam]
                  exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun m _ => if_pos (hg j m)
                rw [e, div_mul_eq_mul_div, eq_div_iff (hpos l0).ne']
                exact hinv _ _ hl hl0 (hYsk _ _ _ _)
              · rw [hQv _ hl]
                have hc := ((hYv x.1 cs l0 x.2).1 hl0).1
                have hn : ¬ ∀ j m, P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset :=
                  fun h => hl ((hYv x.1 cs l x.2).2 ⟨hc, h⟩)
                obtain ⟨j, hj⟩ := not_forall.1 hn
                obtain ⟨m, hjm⟩ := not_forall.1 hj
                have e0 : (∏ j, ∏ m, (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                    then P.lam (l j m) else 0)) = 0 :=
                  Finset.prod_eq_zero (Finset.mem_univ j)
                    (Finset.prod_eq_zero (Finset.mem_univ m) (if_neg hjm))
                rw [e0, mul_zero]
            · refine ⟨0, fun l => ?_⟩
              rw [zero_mul]
              exact hQv _ fun h => hex ⟨l, h⟩
          -- probabilities as finite sums
          have hinjx : ∀ x : List (T × ℕ), Function.Injective
              (fun p : (Fin x.length → C) × ((j : Fin x.length) → Fin (x.get j).2 → C) =>
                Y x p.1 p.2) := by
            intro x p q hpq
            have := hYi x _ _ _ _ hpq
            exact Prod.ext this.1 this.2
          have hprob : ∀ (x : List (T × ℕ)) (E : CState C T → Prop), (∀ y, E y → desc y = x) →
              prob Q E = ∑ cs : Fin x.length → C, ∑ l : ((j : Fin x.length) → Fin (x.get j).2 → C),
                (if E (Y x cs l) then Q (Y x cs l) else 0) := by
            intro x E hE
            have hsupp : Function.support (Set.indicator {y | E y} Q) ⊆ Set.range
                (fun p : (Fin x.length → C) × ((j : Fin x.length) → Fin (x.get j).2 → C) =>
                Y x p.1 p.2) := by
              intro y hy
              have hy' := Function.mem_support.1 hy
              have h1 : E y := by
                by_contra h
                exact hy' (Set.indicator_of_notMem (by exact h) Q)
              have h2 : Valid P y := by
                by_contra h
                apply hy'
                rw [Set.indicator_of_mem (by exact h1)]
                exact hQv y h
              obtain ⟨cs, l, h⟩ := hYs x y h2 (hE y h1)
              exact ⟨(cs, l), h.symm⟩
            have e1 := (hinjx x).tsum_eq hsupp
            have e2 : prob Q E = ∑' y, Set.indicator {y | E y} Q y := rfl
            rw [e2, ← e1, tsum_fintype, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun cs _ => Finset.sum_congr rfl fun l _ => ?_
            exact Set.indicator_apply _ _ _
          -- splitting the eta product
          have hsplit : ∀ (f : ℕ → ℝ) (a b : ℕ), ∏ j ∈ Icc 1 (a + b), f j =
              (∏ j ∈ Icc 1 a, f j) * ∏ j ∈ Icc 1 b, f (a + j) := by
            intro f a b
            induction b with
            | zero => simp
            | succ b ih =>
              rw [← add_assoc, Finset.prod_Icc_succ_top (by omega), ih,
                Finset.prod_Icc_succ_top (by omega), mul_assoc, add_assoc]
          have hcf : ∀ x : State T, commonFactor P x.1 *
              ∏ j : Fin x.1.length, alpha P ((toks x.1).take (j + 1)) ^ (x.1.get j).2 =
              prob Q (fun y => desc y = x.1) := by
            intro x
            rw [hdesc x]
            unfold commonFactor weight weightL phi
            rw [hsplit]
            ring
          -- summability and reindexing
          have hFs : Summable (fun y => (Q y : ℂ) * ∏ c, z c ^ Mtot y c) := by
            refine Summable.of_norm_bounded hQ1.summable fun y => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hQ0 y), norm_prod]
            refine mul_le_of_le_one_right (hQ0 y) (Finset.prod_le_one (fun c _ => norm_nonneg _) ?_)
            intro c _
            rw [norm_pow]
            exact pow_le_one₀ (norm_nonneg _) (hz c).le
          have hinj : Function.Injective (fun p : (Σ x : State T, (Fin x.1.length → C) ×
              ((j : Fin x.1.length) → Fin (x.1.get j).2 → C)) => Y p.1.1 p.2.1 p.2.2) := by
            rintro ⟨x, p⟩ ⟨x', p'⟩ h
            have hx : x = x' := by
              apply Subtype.ext
              have := congrArg desc h
              rwa [hYd, hYd] at this
            subst hx
            exact congrArg (Sigma.mk x) (hinjx x.1 h)
          have hF0 : ∀ y, y ∉ Set.range (fun p : (Σ x : State T, (Fin x.1.length → C) ×
              ((j : Fin x.1.length) → Fin (x.1.get j).2 → C)) => Y p.1.1 p.2.1 p.2.2) →
              (Q y : ℂ) * ∏ c, z c ^ Mtot y c = 0 := by
            intro y hy
            have : ¬ Valid P y := by
              intro hv
              apply hy
              obtain ⟨cs, l, h⟩ := hYs (desc y) y hv rfl
              have hn : ((desc y).map Prod.fst).Nodup := by
                have h3 := hYt (desc y) cs l
                rw [← h] at h3
                have h4 := hv.1
                rw [h3] at h4
                exact h4
              exact ⟨⟨⟨desc y, hn⟩, cs, l⟩, h.symm⟩
            rw [hQv y this]
            simp
          have hsum := (hinj.hasSum_iff hF0).2 hFs.hasSum
          refine HasSum.sigma hsum fun x => ?_
          -- the fibre identity
          choose H hH using hfac x
          have hpx := hcf x
          have hU : ∀ S : Finset T, lamU P S = ∑ c, (if P.tok c ⊆ S then P.lam c else 0) := by
            intro S
            unfold lamU
            rw [Finset.sum_filter]
          have hpxc : ∀ cs : Fin x.1.length → C,
              prob Q (fun y => desc y = x.1 ∧ holderTypes y = List.ofFn cs) =
                H cs * ∏ j : Fin x.1.length, lamU P ((toks x.1).take (j + 1)).toFinset ^ (x.1.get j).2 := by
            intro cs
            rw [hprob x.1 _ (fun y hy => hy.1), Finset.sum_eq_single cs]
            · refine Eq.trans (Finset.sum_congr rfl (g := fun l : ((j : Fin x.1.length) → Fin (x.1.get j).2 → C) => H cs * ∏ j, ∏ m,
                (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset then P.lam (l j m) else 0))
                fun l _ => ?_) ?_
              · rw [if_pos ⟨hYd _ _ _, hYh _ _ _⟩, hH]
              rw [← Finset.mul_sum]
              rw [hexp ℝ x.1.length (fun j => (x.1.get j).2) (fun j c =>
                if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then P.lam c else 0)]
              refine congrArg₂ (· * ·) rfl ?_
              exact Finset.prod_congr rfl fun j _ => by rw [hU]
            · intro cs' _ hne
              refine Finset.sum_eq_zero fun l _ => if_neg ?_
              rintro ⟨_, h⟩
              rw [hYh] at h
              exact hne (List.ofFn_injective h)
            · intro h
              exact absurd (Finset.mem_univ _) h
          have hpxs : prob Q (fun y => desc y = x.1) = ∑ cs : Fin x.1.length → C,
              prob Q (fun y => desc y = x.1 ∧ holderTypes y = List.ofFn cs) := by
            rw [hprob x.1 (fun y => desc y = x.1) (fun y hy => hy)]
            refine Finset.sum_congr rfl fun cs _ => ?_
            rw [hprob x.1 _ (fun y hy => hy.1), Finset.sum_eq_single cs]
            · refine Finset.sum_congr rfl fun l _ => ?_
              rw [if_pos (hYd _ _ _), if_pos ⟨hYd _ _ _, hYh _ _ _⟩]
            · intro cs' _ hne
              refine Finset.sum_eq_zero fun l _ => if_neg ?_
              rintro ⟨_, h⟩
              rw [hYh] at h
              exact hne (List.ofFn_injective h)
            · intro h
              exact absurd (Finset.mem_univ _) h
          have hp0 : ∀ E : CState C T → Prop, 0 ≤ prob Q E := fun E =>
            tsum_nonneg fun y => Set.indicator_nonneg (fun y _ => hQ0 y) y
          have hG : ∀ cs : Fin x.1.length → C,
              prob Q (fun y => desc y = x.1) * Gcond Q x.1 (List.ofFn cs) =
                H cs * ∏ j : Fin x.1.length, lamU P ((toks x.1).take (j + 1)).toFinset ^ (x.1.get j).2 := by
            intro cs
            rw [← hpxc cs]
            unfold Gcond
            by_cases h0 : prob Q (fun y => desc y = x.1) = 0
            · have h5 := h0
              rw [hpxs, Finset.sum_eq_zero_iff_of_nonneg (fun cs _ => hp0 _)] at h5
              rw [h5 cs (Finset.mem_univ _), h0, zero_mul]
            · exact mul_div_cancel₀ _ h0
          have hUt : ∀ l : List T, (lamU P l.toFinset : ℂ) * ∑ c, (theta P l c : ℂ) * z c =
              ∑ c, (if P.tok c ⊆ l.toFinset then (P.lam c : ℂ) else 0) * z c := by
            intro l
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← mul_assoc]
            congr 1
            unfold theta
            by_cases hc : P.tok c ⊆ l.toFinset
            · rw [if_pos hc, if_pos hc]
              have hne : lamU P l.toFinset ≠ 0 := by
                have h6 : P.lam c ≤ lamU P l.toFinset := by
                  unfold lamU
                  exact Finset.single_le_sum (f := P.lam) (fun c _ => (hlam c).le)
                    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
                exact ((hlam c).trans_le h6).ne'
              rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hne]
            · rw [if_neg hc, if_neg hc]
              simp
          have hfib : (commonFactor P x.1 : ℂ) *
                (∑ cs : Fin x.1.length → C, (Gcond Q x.1 (List.ofFn cs) : ℂ) * ∏ j, z (cs j)) *
                ∏ j : Fin x.1.length,
                  ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
                    ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2 =
              ∑ p : (Fin x.1.length → C) × ((j : Fin x.1.length) → Fin (x.1.get j).2 → C),
                (Q (Y x.1 p.1 p.2) : ℂ) * ∏ c, z c ^ Mtot (Y x.1 p.1 p.2) c := by
            rw [Fintype.sum_prod_type]
            have hL : ∀ cs : Fin x.1.length → C,
                ∑ l : ((j : Fin x.1.length) → Fin (x.1.get j).2 → C),
                  (Q (Y x.1 cs l) : ℂ) * ∏ c, z c ^ Mtot (Y x.1 cs l) c =
                (H cs : ℂ) * (∏ j, z (cs j)) * ∏ j : Fin x.1.length,
                  ((lamU P ((toks x.1).take (j + 1)).toFinset : ℂ) *
                    ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2 := by
              intro cs
              have e1 : ∀ l : ((j : Fin x.1.length) → Fin (x.1.get j).2 → C),
                  (Q (Y x.1 cs l) : ℂ) * ∏ c, z c ^ Mtot (Y x.1 cs l) c =
                  (H cs : ℂ) * (∏ j, z (cs j)) * ∏ j, ∏ m,
                    ((if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                      then (P.lam (l j m) : ℂ) else 0) * z (l j m)) := by
                intro l
                rw [hYm, hH]
                have e2 : ((∏ j, ∏ m, (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                    then P.lam (l j m) else 0) : ℝ) : ℂ) = ∏ j, ∏ m,
                    (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                      then (P.lam (l j m) : ℂ) else 0) := by
                  rw [Complex.ofReal_prod]
                  refine Finset.prod_congr rfl fun j _ => ?_
                  rw [Complex.ofReal_prod]
                  refine Finset.prod_congr rfl fun m _ => ?_
                  rw [apply_ite Complex.ofReal, Complex.ofReal_zero]
                have e3 : (∏ j, ∏ m, ((if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                      then (P.lam (l j m) : ℂ) else 0) * z (l j m))) =
                    (∏ j, ∏ m, (if P.tok (l j m) ⊆ ((toks x.1).take (j + 1)).toFinset
                      then (P.lam (l j m) : ℂ) else 0)) * ∏ j, ∏ m, z (l j m) := by
                  rw [← Finset.prod_mul_distrib]
                  exact Finset.prod_congr rfl fun j _ => Finset.prod_mul_distrib
                rw [Complex.ofReal_mul, e2, e3]
                ring
              rw [Finset.sum_congr rfl (fun l _ => e1 l), ← Finset.mul_sum]
              rw [hexp ℂ x.1.length (fun j => (x.1.get j).2) (fun j c =>
                (if P.tok c ⊆ ((toks x.1).take (j + 1)).toFinset then (P.lam c : ℂ) else 0) * z c)]
              refine congrArg₂ (· * ·) rfl ?_
              exact Finset.prod_congr rfl fun j _ => by rw [hUt]
            rw [Finset.sum_congr rfl (fun cs _ => hL cs)]
            have hpxC : (commonFactor P x.1 : ℂ) *
                ∏ j : Fin x.1.length, (alpha P ((toks x.1).take (j + 1)) : ℂ) ^ (x.1.get j).2 =
                (prob Q (fun y => desc y = x.1) : ℂ) := by
              rw [← hpx]
              push_cast
              rfl
            have hGC : ∀ cs : Fin x.1.length → C,
                (prob Q (fun y => desc y = x.1) : ℂ) * (Gcond Q x.1 (List.ofFn cs) : ℂ) =
                (H cs : ℂ) * ∏ j : Fin x.1.length,
                  (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ) ^ (x.1.get j).2 := by
              intro cs
              rw [← Complex.ofReal_mul, hG cs]
              push_cast
              rfl
            have hA : (∏ j : Fin x.1.length, ((alpha P ((toks x.1).take (j + 1)) : ℂ) *
                  ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2) =
                (∏ j : Fin x.1.length, (alpha P ((toks x.1).take (j + 1)) : ℂ) ^ (x.1.get j).2) *
                ∏ j : Fin x.1.length,
                  (∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2 := by
              rw [← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _
            have hB : (∏ j : Fin x.1.length, ((lamU P ((toks x.1).take (j + 1)).toFinset : ℂ) *
                  ∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2) =
                (∏ j : Fin x.1.length, (lamU P ((toks x.1).take (j + 1)).toFinset : ℂ) ^ (x.1.get j).2) *
                ∏ j : Fin x.1.length,
                  (∑ c, (theta P ((toks x.1).take (j + 1)) c : ℂ) * z c) ^ (x.1.get j).2 := by
              rw [← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _
            have hR : ∀ a S b t : ℂ, a * S * (b * t) = (a * b) * S * t := by
              intro a S b t
              ring
            rw [hA, hB, hR, hpxC, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun cs _ => ?_
            rw [← mul_assoc, hGC cs]
            ring
          rw [hfib]
          exact hasSum_fintype _
        classical
        obtain ⟨hQ0, hQ1, hQv, hrow, hin, hbal⟩ := id hQ
        obtain ⟨hlam, htok, hass0, hassn, hass1, hs0, heta⟩ := id hS
        obtain ⟨ins, hins⟩ : ∃ ins : ℕ → C → T → CState C T → CState C T, ∀ p c t y,
            ins p c t y = y.take p ++ (c, some t) ::
            (y.drop p).map (fun e => if e.2 = some t then (e.1, none) else e) := ⟨_, fun _ _ _ _ => rfl⟩
        obtain ⟨lamIn, hlamIn⟩ : ∃ lamIn : CState C T → ℝ, ∀ y,
            lamIn y = (y.map (fun e => if e.2 = none then P.lam e.1 else 1)).prod := ⟨_, fun _ => rfl⟩
        obtain ⟨Pi, hPi⟩ : ∃ Pi : CState C T → ℝ, ∀ y, Pi y = piLam P (heldToks y) * lamIn y *
            (∏ q ∈ range y.length, (kfun P (heldToks (y.take (q + 1))))⁻¹) *
            ∏ q ∈ range y.length, (P.eta (q + 1))⁻¹ := ⟨_, fun _ => rfl⟩
        obtain ⟨wd, hwd⟩ : ∃ wd : CState C T → List (Option C × Option T), ∀ y,
            wd y = y.map (fun e => (if e.2 = none then some e.1 else none, e.2)) := ⟨_, fun _ => rfl⟩
        obtain ⟨sk, hsk⟩ : ∃ sk : CState C T → List (Option (C × Option T)), ∀ y,
            sk y = y.map (fun e => if e.2 = none then none else some e) := ⟨_, fun _ => rfl⟩
        obtain ⟨R, hR0, hRn, hRt⟩ : ∃ R : CState C T → ℝ, R [] = 0 ∧
            (∀ y c, R (y ++ [(c, none)]) = P.lam c) ∧
            (∀ y c t, R (y ++ [(c, some t)]) = P.lam c * P.assign c (held y) t) :=
          ⟨fun y => match y.getLast? with
            | none => 0
            | some (c, none) => P.lam c
            | some (c, some t) => P.lam c * P.assign c (held y.dropLast) t, by simp, by simp, by simp⟩
        obtain ⟨Inf, hInf⟩ : ∃ Inf : (CState C T → ℝ) → CState C T → ℝ, ∀ f y,
            Inf f y = R y * f y.dropLast + ∑ p ∈ range (y.length + 1), ∑ c, ∑ t,
            P.eta (y.length + 1) * P.s (heldToks (y.take p) ++ [t]) * f (ins p c t y) := ⟨_, fun _ _ => rfl⟩
        obtain ⟨A, hA⟩ : ∃ A : ℕ → Finset (CState C T), ∀ n y, y ∈ A n ↔ y.length = n :=
          ⟨fun n => (List.finite_length_eq (C × Option T) n).toFinset, fun n y => by simp⟩
        obtain ⟨Y, hY⟩ : ∃ Y : (x : List (T × ℕ)) → (Fin x.length → C) →
            ((j : Fin x.length) → Fin (x.get j).2 → C) → CState C T, ∀ x cs l,
            Y x cs l = (List.finRange x.length).flatMap (fun j =>
            (cs j, some (x.get j).1) :: List.ofFn (fun m => (l j m, none))) := ⟨_, fun _ _ _ => rfl⟩
        obtain ⟨B, hB⟩ : ∃ B : ℕ → Finset (State T), ∀ n x, x ∈ B n ↔ phi x.1 = n := by
          have hfin : ∀ n, {x : State T | phi x.1 = n}.Finite := by
            intro n
            have h0 : {l : List (T × Fin (n+1)) | l.length ≤ n}.Finite := List.finite_length_le _ n
            have h3 := (h0.image (fun l => l.map (fun e => (e.1, e.2.val)))).preimage
              (f := (Subtype.val : State T → List (T × ℕ))) Subtype.val_injective.injOn
            refine h3.subset ?_
            intro x hx
            simp only [Set.mem_setOf_eq, phi] at hx
            simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
            refine ⟨x.1.map (fun e => (e.1, Fin.ofNat (n+1) e.2)), by simp; omega, ?_⟩
            rw [List.map_map]
            conv_rhs => rw [← List.map_id x.1]
            apply List.map_congr_left
            intro e he
            have h4 : e.2 ≤ (x.1.map Prod.snd).sum := List.le_sum_of_mem (List.mem_map_of_mem he)
            simp only [Function.comp, id]
            ext
            · rfl
            · simp [Fin.ofNat]; omega
          exact ⟨fun n => (hfin n).toFinset, fun n x => by simp⟩
        obtain ⟨hYb, hYd, hYh, hYi, hYs, hYt, hYl⟩ := L0a Y hY
        obtain ⟨hYv, hYm, hYlam, hYsk, hYk, hYw⟩ := L0b Y hY lamIn hlamIn sk hsk wd hwd
        have hc0 := L4c
        have hq := L1
        have hlev := L2 A hA
        have hcut := (L45M hc0 Q hQ A hA hq hlev).1
        obtain ⟨u, hu0, hu1, hupos, huQ, hulim⟩ := (L45M hc0 Q hQ A hA hq hlev).2
        have huv : ∀ n y, ¬ Valid P y → u n y = 0 := fun n y hy =>
          le_antisymm ((huQ n y).trans (hQv y hy).le) (hupos n y)
        have hne : ∀ y, Valid P y → y ≠ [] → heldToks y ≠ [] := by
          intro y hy hy0 hh
          obtain ⟨e, l, rfl⟩ := List.exists_cons_of_ne_nil hy0
          obtain ⟨c, o⟩ := e
          cases o with
          | some t => simp [heldToks] at hh
          | none =>
            have h3 := hy.2.2 0 (by simp) (by simp)
            obtain ⟨t, ht⟩ := htok c
            have h4 := h3 (by simpa using ht)
            simp [held, heldToks] at h4
        have hk0 : ∀ l, 0 ≤ kfun P l := fun l => Finset.sum_nonneg fun _ _ => hs0 _
        have hkp : ∀ y, Valid P y → y ≠ [] → 0 < kfun P (heldToks y) := fun y hy h => hk _ hy.1 (hne y hy h)
        have hetal : ∀ y : CState C T, y ≠ [] → 0 < P.eta y.length := fun y h =>
          heta _ (List.length_pos_iff.2 h)
        have hlT : 0 ≤ lamTot P := Finset.sum_nonneg fun c _ => (hlam c).le
        have hqp : ∀ y, Valid P y → y ≠ [] → 0 < lamTot P + P.eta y.length * kfun P (heldToks y) :=
          fun y hy h => add_pos_of_nonneg_of_pos hlT (mul_pos (hetal y h) (hkp y hy h))
        have hul : ∀ n y, Valid P y → y ≠ [] → u (n+1) y * (lamTot P + P.eta y.length * kfun P (heldToks y)) = Inf (u n) y := by
          intro n y hy h
          rw [hu1, if_neg h, (L3 ins hins R hR0 hRn hRt Inf hInf (u n) (huv n) y hy).tsum_eq]
          exact div_mul_cancel₀ _ (hqp y hy h).ne'
        have hsk0 : ∀ y, sk y = sk [] → y = [] := by
          intro y h; rw [hsk, hsk] at h; simpa using h
        -- heldToks from sk
        have hskT : ∀ y, heldToks y = (sk y).filterMap (fun o => o.bind Prod.snd) := by
          intro y; rw [hsk]
          simp only [heldToks, List.filterMap_map]
          congr 1
          funext e
          rcases e with ⟨c, _ | t⟩ <;> simp
        have hskl : ∀ y, y.length = (sk y).length := by intro y; rw [hsk]; simp
        have hwdT : ∀ y, heldToks y = (wd y).filterMap Prod.snd := by
          intro y; rw [hwd]
          simp only [heldToks, List.filterMap_map]
          congr 1
        have hwdl : ∀ y, y.length = (wd y).length := by intro y; rw [hwd]; simp
        have hinvu : ∀ n y y', Valid P y → Valid P y' → sk y = sk y' → u n y * lamIn y' = u n y' * lamIn y := by
          intro n
          induction n with
          | zero => intro y y' _ _ _; simp [hu0]
          | succ n ih =>
            intro y y' hy hy' hs
            by_cases h : y = []
            · subst h
              have : y' = [] := hsk0 y' hs.symm
              subst this; rfl
            · have h' : y' ≠ [] := by
                rintro rfl; exact h (hsk0 y hs)
              have e1 := hul n y hy h
              have e2 := hul n y' hy' h'
              have e3 := L6 ins hins R hR0 hRn hRt Inf hInf lamIn hlamIn sk hsk (u n) (huv n) ih y y' hy hy' hs
              have e4 : heldToks y' = heldToks y := by rw [hskT, hskT, hs]
              have e5 : y'.length = y.length := by rw [hskl, hskl y, hs]
              rw [e4, e5] at e2
              rw [← e1, ← e2] at e3
              apply mul_right_cancel₀ (hqp y hy h).ne'
              linarith
        have hinv : ∀ y y', Valid P y → Valid P y' → sk y = sk y' → Q y * lamIn y' = Q y' * lamIn y := by
          intro y y' hy hy' hs
          refine tendsto_nhds_unique ((hulim y).mul_const (lamIn y')) ?_
          simp_rw [hinvu _ y y' hy hy' hs]
          exact (hulim y').mul_const _
        have hPiwd : ∀ y y', wd y = wd y' → Pi y = Pi y' := by
          intro y y' h
          have hl : y.length = y'.length := by rw [hwdl, hwdl y', h]
          have hp : ∀ q, heldToks (y.take q) = heldToks (y'.take q) := by
            intro q
            rw [hwdT, hwdT (y'.take q), hwd, hwd, List.map_take, List.map_take, ← hwd, ← hwd, h]
          have hlamw : ∀ y, lamIn y = ((wd y).map (fun e => match e.1 with | some c => P.lam c | none => 1)).prod := by
            intro y
            rw [hlamIn, hwd, List.map_map]
            congr 2
            funext e
            rcases e with ⟨c, _ | t⟩ <;> simp
          rw [hPi, hPi, hlamw, hlamw y', h, hl, hwdT y, hwdT y', h]
          simp_rw [hp]
        have hLT0 : ∀ S t, 0 ≤ lamTok P S t := fun S t =>
          Finset.sum_nonneg fun c _ => mul_nonneg (hlam c).le (hass0 c S t)
        have hPi0 : ∀ y, 0 ≤ Pi y := by
          intro y
          rw [hPi]
          refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
          · exact Finset.prod_nonneg fun _ _ => hLT0 _ _
          · rw [hlamIn]
            apply List.prod_nonneg
            intro a ha
            obtain ⟨e, _, rfl⟩ := List.mem_map.1 ha
            split_ifs
            · exact (hlam _).le
            · exact zero_le_one
          · exact Finset.prod_nonneg fun _ _ => inv_nonneg.2 (hk0 _)
          · exact Finset.prod_nonneg fun q _ => inv_nonneg.2 (heta _ (by omega)).le
        have hPinil : Pi [] = 1 := by
          have e : piLam P ([] : List T) = 1 := Fin.prod_univ_zero _
          rw [hPi, hlamIn, show heldToks ([] : CState C T) = [] from rfl, e]; simp
        have hSu : ∀ n y (F : Finset (CState C T)), (∀ y1 ∈ F, wd y1 = wd y) → ∑ y1 ∈ F, u n y1 ≤ Q [] * Pi y := by
          intro n
          induction n with
          | zero => intro y F _; simp only [hu0, Finset.sum_const_zero]; exact mul_nonneg (hQ0 _) (hPi0 _)
          | succ n ih =>
            intro y F hF
            have e0 : ∑ y1 ∈ F, u (n+1) y1 = ∑ y1 ∈ F.filter (Valid P), u (n+1) y1 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun y1 _ => ?_
              split_ifs with h
              · rfl
              · exact huv _ _ h
            rw [e0]
            rcases (F.filter (Valid P)).eq_empty_or_nonempty with h | ⟨y2, hy2⟩
            · rw [h, Finset.sum_empty]; exact mul_nonneg (hQ0 _) (hPi0 _)
            · obtain ⟨hy2F, hy2v⟩ := Finset.mem_filter.1 hy2
              have hw2 := hF y2 hy2F
              have hF' : ∀ y1 ∈ F.filter (Valid P), Valid P y1 ∧ wd y1 = wd y2 := fun y1 h =>
                ⟨(Finset.mem_filter.1 h).2, (hF y1 (Finset.mem_filter.1 h).1).trans hw2.symm⟩
              rw [← hPiwd y2 y hw2]
              by_cases h2n : y2 = []
              · subst h2n
                have hsub : F.filter (Valid P) ⊆ {[]} := by
                  intro y1 h
                  have := (hF' y1 h).2
                  rw [hwd, hwd] at this
                  simpa using this
                refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hupos _ _)).trans ?_
                rw [Finset.sum_singleton, hPinil, mul_one]
                exact huQ _ _
              · have hc := L7C ins hins lamIn hlamIn Pi hPi wd hwd
                  (fun y c t hy ht => (L7M lamIn hlamIn Pi hPi t).1 ins hins y hy c ht)
                  (fun a b g t c g' hy => (L7M lamIn hlamIn Pi hPi t).2 a b g hy c g')
                  (u n) (hupos n) (huv n) (Q []) (hQ0 _) ih y2 hy2v _ hF'
                have hd := L7D lamIn hlamIn Pi hPi wd hwd R hR0 hRn hRt
                  (u n) (hupos n) (huv n) (Q []) (hQ0 _) ih y2 hy2v _ hF'
                have e1 : (∑ y1 ∈ F.filter (Valid P), u (n+1) y1) *
                    (lamTot P + P.eta y2.length * kfun P (heldToks y2)) =
                    ∑ y1 ∈ F.filter (Valid P), Inf (u n) y1 := by
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun y1 h => ?_
                  obtain ⟨hv1, hw1⟩ := hF' y1 h
                  have e4 : heldToks y1 = heldToks y2 := by rw [hwdT, hwdT y2, hw1]
                  have e5 : y1.length = y2.length := by rw [hwdl, hwdl y2, hw1]
                  have hn1 : y1 ≠ [] := by
                    rintro rfl
                    apply h2n
                    exact List.length_eq_zero_iff.1 (by rw [← e5]; rfl)
                  rw [← hul n y1 hv1 hn1, e4, e5]
                have e2 : ∑ y1 ∈ F.filter (Valid P), Inf (u n) y1 ≤ Q [] * Pi y2 *
                    (lamTot P + P.eta y2.length * kfun P (heldToks y2)) := by
                  simp_rw [hInf]
                  rw [Finset.sum_add_distrib, mul_add]
                  linarith
                rw [← e1] at e2
                exact le_of_mul_le_mul_right e2 (hqp y2 hy2v h2n)
        have hSQ : ∀ y (F : Finset (CState C T)), (∀ y1 ∈ F, wd y1 = wd y) → ∑ y1 ∈ F, Q y1 ≤ Q [] * Pi y := by
          intro y F hF
          exact le_of_tendsto' (tendsto_finset_sum F fun y1 _ => hulim y1) (fun n => hSu n y F hF)
        have hle := L9 Y hY lamIn hlamIn Pi hPi sk hsk wd hwd hYb hYd hYh hYi hYs hYt hYl hYv hYm hYlam hYsk hYk hYw
          Q hQ0 hQv (Q []) (hQ0 _) hSQ
        have hvd : ∀ y, Valid P y → toks (desc y) = heldToks y ∧ phi (desc y) = y.length := by
          intro y hy
          obtain ⟨cs, l, h⟩ := hYs (desc y) y hy rfl
          have a1 := hYt (desc y) cs l
          have a2 := hYl (desc y) cs l
          rw [← h] at a1 a2
          exact ⟨a1.symm, a2.symm⟩
        have hprob : ∀ n, ∀ x ∈ B n, prob Q (fun y => desc y = x.1) = ∑ y ∈ A n, if desc y = x.1 then Q y else 0 := by
          intro n x hx
          unfold prob
          rw [tsum_eq_sum (s := A n)]
          · refine Finset.sum_congr rfl fun y _ => ?_
            simp [Set.indicator_apply]
          · intro y hy
            rw [Set.indicator_apply]
            split_ifs with h
            · by_contra hne0
              have hv : Valid P y := by by_contra hv; exact hne0 (hQv y hv)
              apply hy
              rw [hA, ← (hvd y hv).2, ← (hB n x).1 hx]
              rw [show desc y = x.1 from h]
            · rfl
        have hlevel : ∀ n (G : List T → ℝ), ∑ x ∈ B n, G (toks x.1) * prob Q (fun y => desc y = x.1) =
            ∑ y ∈ A n, G (heldToks y) * Q y := by
          intro n G
          have e1 : ∑ x ∈ B n, G (toks x.1) * prob Q (fun y => desc y = x.1) =
              ∑ x ∈ B n, ∑ y ∈ A n, (if desc y = x.1 then G (heldToks y) * Q y else 0) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [hprob n x hx, Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            split_ifs with h
            · by_cases hv : Valid P y
              · rw [← (hvd y hv).1, h]
              · rw [hQv y hv]; simp
            · simp
          rw [e1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun y hy => ?_
          by_cases hv : Valid P y
          · have hnd : ((desc y).map Prod.fst).Nodup := by
              have := hv.1
              rw [← (hvd y hv).1] at this
              exact this
            rw [Finset.sum_eq_single (⟨desc y, hnd⟩ : State T)]
            · simp
            · intro x _ hx
              rw [if_neg]
              intro h
              exact hx (Subtype.ext h.symm)
            · intro h
              exfalso
              apply h
              rw [hB]
              simp only
              rw [(hvd y hv).2]
              exact (hA n y).1 hy
          · rw [hQv y hv]; simp
        have hBA := L10 B hB
        have hEq : ∀ n, ∀ x ∈ B n, prob Q (fun y => desc y = x.1) = Q [] * weight P x := by
          intro n
          induction n with
          | zero =>
            intro x hx
            have hx0 : x = State.empty := by
              have := (hB 0 x).1 hx
              unfold phi at this
              apply Subtype.ext
              show x.1 = []
              exact List.length_eq_zero_iff.1 (by omega)
            have hB0 : B 0 = {State.empty} := by
              ext x'
              rw [hB, Finset.mem_singleton]
              constructor
              · intro this
                unfold phi at this
                apply Subtype.ext
                show x'.1 = []
                exact List.length_eq_zero_iff.1 (by omega)
              · rintro rfl; rfl
            have hA0 : A 0 = {[]} := by
              ext y; rw [hA, Finset.mem_singleton, List.length_eq_zero_iff]
            have h3 := hlevel 0 (fun _ => 1)
            rw [hB0, hA0, Finset.sum_singleton, Finset.sum_singleton, one_mul, one_mul] at h3
            rw [hx0, h3]
            have : weight P (State.empty : State T) = 1 := by
              have e1 : piLam P ([] : List T) = 1 := Fin.prod_univ_zero _
              have e2 : piK P ([] : List T) = 1 := Fin.prod_univ_zero _
              have e3 : ∏ j : Fin ([] : List (T × ℕ)).length,
                alpha P ((toks ([] : List (T × ℕ))).take (j + 1)) ^ (([] : List (T × ℕ)).get j).2 = 1 := Fin.prod_univ_zero _
              show weightL P [] = 1
              unfold weightL
              rw [e3, show toks ([] : List (T × ℕ)) = [] from rfl, e1, e2]
              simp [phi]
            rw [this, mul_one]
          | succ n ih =>
            have h3 := hlevel n (fun _ => lamTot P)
            have h4 := hlevel (n+1) (fun l => P.eta (n+1) * kfun P l)
            have h5 := hcut n
            have h6 := hBA n
            have h7 : ∑ x ∈ B n, lamTot P * prob Q (fun y => desc y = x.1) = Q [] * (lamTot P * ∑ x ∈ B n, weight P x) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [ih x hx]; ring
            have h8 : ∑ x ∈ B (n+1), P.eta (n+1) * kfun P (toks x.1) * (Q [] * weight P x - prob Q (fun y => desc y = x.1)) ≤ 0 := by
              have h9 := mul_le_mul_of_nonneg_left h6 (hQ0 [])
              rw [← h7, h3, h5, ← h4, Finset.mul_sum] at h9
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              have h10 : ∑ x ∈ B (n+1), P.eta (n+1) * kfun P (toks x.1) * (Q [] * weight P x) =
                ∑ x ∈ B (n+1), Q [] * (P.eta (n+1) * kfun P (toks x.1) * weight P x) :=
                Finset.sum_congr rfl fun x _ => by ring
              rw [h10]; linarith
            have hkx : ∀ x ∈ B (n+1), 0 < P.eta (n+1) * kfun P (toks x.1) := by
              intro x hx
              refine mul_pos (heta _ (by omega)) (hk _ x.2 ?_)
              intro h
              have hx0 : x.1 = [] := by simpa [toks] using h
              have := (hB _ x).1 hx
              rw [hx0] at this
              simp [phi] at this
            have hnn : ∀ x ∈ B (n+1), 0 ≤ P.eta (n+1) * kfun P (toks x.1) * (Q [] * weight P x - prob Q (fun y => desc y = x.1)) :=
              fun x hx => mul_nonneg (hkx x hx).le (sub_nonneg.2 (hle x))
            intro x hx
            have h11 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm h8 (Finset.sum_nonneg hnn)) x hx
            have h12 := (mul_eq_zero.1 h11).resolve_left (hkx x hx).ne'
            linarith
        have hEq' : ∀ x : State T, prob Q (fun y => desc y = x.1) = Q [] * weight P x := fun x =>
          hEq _ x ((hB _ x).2 rfl)
        have hsum1 : HasSum (fun x : State T => prob Q (fun y => desc y = x.1)) 1 := by
          let d : CState C T → State T := fun y =>
            if h : ((desc y).map Prod.fst).Nodup then ⟨desc y, h⟩ else State.empty
          have h3 := hQ1.tsum_fiberwise d
          refine Eq.subst (motive := fun g : State T → ℝ => HasSum g 1) ?_ h3
          funext x
          symm
          unfold prob
          rw [tsum_subtype (d ⁻¹' {x}) Q]
          refine tsum_congr fun y => ?_
          by_cases hv : Valid P y
          · have hnd : ((desc y).map Prod.fst).Nodup := by
              have := hv.1
              rw [← (hvd y hv).1] at this
              exact this
            have hdy : d y = ⟨desc y, hnd⟩ := dif_pos hnd
            have hiff : d y = x ↔ desc y = x.1 := by
              rw [hdy]; exact Subtype.ext_iff
            simp [Set.indicator_apply, hiff]
          · simp [Set.indicator_apply, hQv y hv]
        have hpz : Q [] = piZero P := by
          have h3 : ∑' x : State T, Q [] * weight P x = 1 := by
            rw [← hsum1.tsum_eq]
            exact tsum_congr fun x => (hEq' x).symm
          rw [tsum_mul_left] at h3
          unfold piZero
          exact eq_inv_of_mul_eq_one_left h3
        exact L11 Y hY lamIn hlamIn sk hsk hYb hYd hYh hYi hYs hYt hYl hYv hYm hYlam hYsk Q hQ0 hQ1 hQv hinv
          (fun x => by rw [hEq' x, hpz]) z hz
