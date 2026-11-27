-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.Supplement.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:25.773888+00:00
-- url     : https://prove2.me/submissions/5f637db1-2104-46ca-b42a-6280ecc64740

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_Gadget

open OnlineMaxWeightMatch
open OnlineMaxWeightMatch.Approx
open OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx

/-- Lemma 3.5: for every optimal online policy on `I_φ`, its expected gain `𝔼[B]` from clause
balls equals `((1 - m^{-4})^{m-1} / (2k)) · OPT_on(φ) + δ` for some `δ ∈ [0, 2/m]`. -/
theorem solution (φ : SSATFormula) (k : ℕ) (hφ : φ.IsThreeCNF) (h1 : φ.NoNegatedRandom)
    (h2 : φ.OccursAtMost k)
    (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length))
    (hπ : policyValue (gadget φ k) π = optOn (gadget φ k)) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ ≤ 2 * ((φ.clauses.length : ℝ))⁻¹ ∧
      clauseGain φ k π =
        (1 - ((φ.clauses.length : ℝ) ^ 4)⁻¹) ^ (φ.clauses.length - 1) / (2 * k) * ssatOpt φ
          + δ := by
            have memins : ∀ {α : Type} {inst : DecidableEq α} (x : α) (s : Finset α) (y : α),
                y ∈ @insert _ _ (@Finset.instInsert _ inst) x s → y = x ∨ y ∈ s := by
              intro α inst x s y hy; exact Finset.mem_insert.1 hy
            have meminsof : ∀ {α : Type} {inst : DecidableEq α} (x : α) (s : Finset α) (y : α),
                y ∈ s → y ∈ @insert _ _ (@Finset.instInsert _ inst) x s := by
              intro α inst x s y hy; exact Finset.mem_insert_of_mem hy
            -- G1
            have G1 : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                ∀ e ∈ π.matchingUpTo a j, e.2.val < j ∧ a e.2 = true := by
              intro π a j
              induction j with
              | zero => simp [OnlinePolicy.matchingUpTo]
              | succ j ih =>
                intro e he
                simp only [OnlinePolicy.matchingUpTo] at he
                split_ifs at he with hj
                · split at he
                  · split_ifs at he with hc
                    · rcases memins _ _ _ he with rfl | he
                      · exact ⟨by simp, hc.1⟩
                      · exact ⟨by have := (ih e he).1; omega, (ih e he).2⟩
                    · exact ⟨by have := (ih e he).1; omega, (ih e he).2⟩
                  · exact ⟨by have := (ih e he).1; omega, (ih e he).2⟩
                · exact ⟨by have := (ih e he).1; omega, (ih e he).2⟩
            -- monotone step
            have Gsub : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                π.matchingUpTo a j ⊆ π.matchingUpTo a (j+1) := by
              intro π a j e he
              simp only [OnlinePolicy.matchingUpTo]
              split_ifs with hj
              · split
                · split_ifs with hc
                  · exact meminsof _ _ _ he
                  · exact he
                · exact he
              · exact he
            have Gmono : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j j' : ℕ), j ≤ j' →
                π.matchingUpTo a j ⊆ π.matchingUpTo a j' := by
              intro π a j j' hjj
              induction j', hjj using Nat.le_induction with
              | base => exact le_refl _
              | succ j' _ ih => exact ih.trans (Gsub π a j')
            -- filter of later = earlier
            have Gfilt : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                ∀ e ∈ π.matchingUpTo a (j+1), e.2.val < j → e ∈ π.matchingUpTo a j := by
              intro π a j e he hlt
              simp only [OnlinePolicy.matchingUpTo] at he
              split_ifs at he with hj
              · split at he
                · split_ifs at he with hc
                  · rcases memins _ _ _ he with rfl | he
                    · simp at hlt
                    · exact he
                  · exact he
                · exact he
              · exact he
            -- new edges: bin was free
            have Gfree : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                ∀ e ∈ π.matchingUpTo a j, ∀ s, (e.1, s) ∉ π.matchingUpTo a e.2.val := by
              intro π a j
              induction j with
              | zero => simp [OnlinePolicy.matchingUpTo]
              | succ j ih =>
                intro e he
                simp only [OnlinePolicy.matchingUpTo] at he
                split_ifs at he with hj
                · split at he
                  · split_ifs at he with hc
                    · rcases memins _ _ _ he with rfl | he
                      · exact hc.2
                      · exact ih e he
                    · exact ih e he
                  · exact ih e he
                · exact ih e he
            have Gcase : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                ∀ e ∈ π.matchingUpTo a (j+1), e ∈ π.matchingUpTo a j ∨ e.2.val = j := by
              intro π a j e he
              simp only [OnlinePolicy.matchingUpTo] at he
              split_ifs at he with hj
              · split at he
                · split_ifs at he with hc
                  · rcases memins _ _ _ he with rfl | he
                    · right; rfl
                    · left; exact he
                  · left; exact he
                · left; exact he
              · left; exact he
            have Gball : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                ∀ e ∈ π.matchingUpTo a j, ∀ e' ∈ π.matchingUpTo a j, e.2 = e'.2 → e = e' := by
              intro π a j
              induction j with
              | zero => simp [OnlinePolicy.matchingUpTo]
              | succ j ih =>
                intro e he e' he' hee
                by_cases hl : e.2.val < j
                · exact ih e (Gfilt π a j e he hl) e' (Gfilt π a j e' he' (by rw [← hee]; exact hl)) hee
                · have h1 : e.2.val = j := by have := (G1 π a _ e he).1; omega
                  simp only [OnlinePolicy.matchingUpTo] at he he'
                  split_ifs at he he' with hj
                  · revert he he'
                    split
                    · split_ifs with hc
                      · intro he he'
                        rcases memins _ _ _ he with rfl | he
                        · rcases memins _ _ _ he' with rfl | he'
                          · rfl
                          · have := (G1 π a j e' he').1; simp [← hee] at this
                        · have := (G1 π a j e he).1; omega
                      · intro he; have := (G1 π a j e he).1; omega
                    · intro he; have := (G1 π a j e he).1; omega
                  · have := (G1 π a j e he).1; omega
            -- prefix dependence
            have Gpre : ∀ (π : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) (a a' : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                (∀ s : Fin (φ.n + φ.clauses.length), s.val < j → a s = a' s) → π.matchingUpTo a j = π.matchingUpTo a' j := by
              intro π a a' j
              induction j with
              | zero => simp [OnlinePolicy.matchingUpTo]
              | succ j ih =>
                intro h
                have h' := ih (fun s hs => h s (by omega))
                simp only [OnlinePolicy.matchingUpTo]
                split_ifs with hj
                · have hf : (fun s : {s : Fin (φ.n + φ.clauses.length) // s ≤ ⟨j, hj⟩} => a s.1) = (fun s => a' s.1) := by
                    funext s; exact h s.1 (by have := s.2; simp [Fin.le_def] at this; omega)
                  rw [hf, h', h ⟨j, hj⟩ (by simp)]
                · exact h'
            have arith : ∀ (m k : ℕ) (S B L E B' L' : ℝ), 1 ≤ m → 1 ≤ k → 0 ≤ S → S ≤ m → L ≤ E → L' = E →
                L' + B' ≤ L + B → (1 - ((m : ℝ) ^ 4)⁻¹) ^ (m - 1) / (2 * k) * S ≤ B' →
                B ≤ S / (2 * k) + (E - L) / 2 →
                0 ≤ B - (1 - ((m : ℝ) ^ 4)⁻¹) ^ (m - 1) / (2 * k) * S ∧
                B - (1 - ((m : ℝ) ^ 4)⁻¹) ^ (m - 1) / (2 * k) * S ≤ 2 * (m : ℝ)⁻¹ := by
              intro m k S B L E B' L' hm1 hk1 hS0 hSm hLE hL' hle hB' C3
              have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
              have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
              set p : ℝ := ((m : ℝ) ^ 4)⁻¹ with hp
              have hp0 : 0 ≤ p := by positivity
              have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hmR)
              have hbern : 1 - ((m - 1 : ℕ) : ℝ) * p ≤ (1 - p) ^ (m - 1) := by
                have := one_add_mul_le_pow (a := -p) (by linarith) (m - 1)
                simpa [sub_eq_add_neg, neg_mul, mul_comm] using this
              have hm1R : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1]; simp
              rw [hm1R] at hbern
              have h2k : (0 : ℝ) < 2 * k := by positivity
              set c := (1 - p) ^ (m - 1) / (2 * k) with hc
              have hgap : 1 / (2 * k) - c ≤ (m - 1) * p / (2 * k) := by
                rw [hc, ← sub_div]; gcongr; linarith
              have hc0 : 0 ≤ c := by
                have : 0 ≤ 1 - p := by linarith
                positivity
              have e1 : S / (2 * k) = 1 / (2 * k) * S := by ring
              refine ⟨by nlinarith, ?_⟩
              have hkey : B - c * S ≤ 2 * ((m - 1) * p / (2 * k)) * S := by
                nlinarith
              refine hkey.trans ?_
              have : 2 * ((m - 1) * p / (2 * k)) * S ≤ 2 * ((m - 1) * p / (2 * k)) * m := by
                have : (0:ℝ) ≤ m - 1 := by linarith
                gcongr
              refine this.trans ?_
              have hm0' : (0:ℝ) < m := by linarith
              have hk0 : (0:ℝ) < k := by linarith
              rw [hp]
              have : 2 * ((m - 1) * ((m:ℝ) ^ 4)⁻¹ / (2 * k)) * m = (m - 1) / (k * m ^ 3) := by
                field_simp
              rw [this, div_le_iff₀ (by positivity)]
              have : (2:ℝ) * (m:ℝ)⁻¹ * (k * m ^ 3) = 2 * k * m ^ 2 := by field_simp
              rw [this]
              nlinarith [mul_le_mul_of_nonneg_left hkR (by positivity : (0:ℝ) ≤ m ^ 2)]
            -- literal part
            let Lit : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length) → ℝ := fun π =>
              ∑ a : Fin (φ.n + φ.clauses.length) → Bool, arrivalProb (gadget φ k) a *
                ∑ e ∈ (π.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2
            let Elit : ℝ := ∑ a : Fin (φ.n + φ.clauses.length) → Bool, arrivalProb (gadget φ k) a *
                ((Finset.univ.filter (fun t : Fin (φ.n + φ.clauses.length) => t.val < φ.n ∧ a t = true)).card : ℝ)
            have hsplit : ∀ π', policyValue (gadget φ k) π' = Lit π' + clauseGain φ k π' := by
              intro π'
              simp only [policyValue, Lit, clauseGain, ← Finset.sum_add_distrib, ← mul_add]
              refine Finset.sum_congr rfl fun a _ => ?_
              congr 1
              exact (Finset.sum_filter_not_add_sum_filter _ _ _).symm
            have : Finite (OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length)) := by
              unfold OnlinePolicy; infer_instance
            have hopt : ∀ π', policyValue (gadget φ k) π' ≤ policyValue (gadget φ k) π := by
              intro π'
              rw [hπ]
              exact le_ciSup (Set.finite_range _).bddAbove π'
            have hm0 : φ.clauses.length = 0 ∨ (1 ≤ φ.clauses.length ∧ 1 ≤ k) := by
              rcases Nat.eq_zero_or_pos φ.clauses.length with h | h
              · left; exact h
              · right; refine ⟨h, ?_⟩
                obtain ⟨C, hC⟩ : ∃ C, C ∈ φ.clauses := List.exists_mem_of_length_pos h
                obtain ⟨hl1, -, -⟩ := hφ C hC
                obtain ⟨l, hl⟩ : ∃ l, l ∈ C := List.exists_mem_of_length_pos (by omega)
                have hk := h2 l.1
                have : 0 < (φ.clauses.filter fun C => C.any fun l' => l'.1 == l.1).length :=
                  List.length_pos_of_mem (List.mem_filter.2 ⟨hC, List.any_eq_true.2 ⟨l, hl, by simp⟩⟩)
                omega
            rcases hm0 with hm0 | ⟨hm1, hk1⟩
            · have hnil : φ.clauses = [] := List.length_eq_zero_iff.1 hm0
              have hB : clauseGain φ k π = 0 := by
                unfold clauseGain
                refine Finset.sum_eq_zero fun a _ => ?_
                rw [Finset.sum_eq_zero, mul_zero]
                intro e he
                have h3 := (Finset.mem_filter.1 he).2
                have h4 := e.2.isLt
                omega
              have hS : ssatOpt φ = 0 := by
                simp [ssatOpt, ssatValue, SSATFormula.numSat, hnil]
              refine ⟨0, le_refl _, by simp [hm0], ?_⟩
              rw [hB, hS]; simp
            have C1 : ∀ π', Lit π' ≤ Elit := by
              intro π'
              refine Finset.sum_le_sum fun a _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun t _ => by
                have := (gadget φ k).p_nonneg t; have := (gadget φ k).p_le_one t
                split_ifs <;> linarith)
              calc ∑ e ∈ (π'.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2
                  ≤ ∑ e ∈ (π'.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (1 : ℝ) := by
                    refine Finset.sum_le_sum fun e he => ?_
                    have := (Finset.mem_filter.1 he).2
                    simp only [gadget]
                    rw [if_pos (by omega)]
                    split_ifs <;> norm_num
                _ = (((π'.matching a).filter (fun e => ¬ φ.n ≤ e.2.val)).card : ℝ) := by simp
                _ = ((((π'.matching a).filter (fun e => ¬ φ.n ≤ e.2.val)).image Prod.snd).card : ℝ) := by
                    rw [Finset.card_image_of_injOn]
                    intro e he e' he' hee
                    exact Gball π' a _ e (Finset.mem_filter.1 he).1 e' (Finset.mem_filter.1 he').1 hee
                _ ≤ _ := by
                    gcongr
                    intro t ht
                    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
                    have hh := Finset.mem_filter.1 he
                    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega,
                      (G1 π' a _ e hh.1).2⟩
            let pl : Fin φ.n → ℝ := fun v => if IsRandomVar v.val then 1 / 2 else 1
            let pc : ℝ := ((φ.clauses.length : ℝ) ^ 4)⁻¹
            let Plit : (Fin φ.n → Bool) → ℝ := fun u => ∏ v, if u v then pl v else 1 - pl v
            let Pcl : (Fin φ.clauses.length → Bool) → ℝ := fun c => ∏ r, if c r then pc else 1 - pc
            have hpc0 : 0 ≤ pc := by positivity
            have hpc1 : pc ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hm1))
            have H1 : ∀ G : (Fin (φ.n + φ.clauses.length) → Bool) → ℝ,
                ∑ a, arrivalProb (gadget φ k) a * G a = ∑ u, ∑ c, Plit u * Pcl c * G (Fin.append u c) := by
              intro G
              rw [← (Fin.appendEquiv φ.n φ.clauses.length).sum_comp, Fintype.sum_prod_type]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun c _ => ?_
              change arrivalProb (gadget φ k) (Fin.append u c) * G (Fin.append u c) = _
              congr 1
              unfold arrivalProb
              rw [Fin.prod_univ_add]
              simp only [Fin.append_left, Fin.append_right, Plit, Pcl, pl, pc, gadget]
              congr 1
              · refine Finset.prod_congr rfl fun v _ => ?_
                simp
              · refine Finset.prod_congr rfl fun r _ => ?_
                simp
            have H3 : ∀ χ : Fin φ.clauses.length → Bool → ℝ, ∑ c, Pcl c * ∏ r, χ r (c r) =
                ∏ r, (pc * χ r true + (1 - pc) * χ r false) := by
              intro χ
              simp only [Pcl, ← Finset.prod_mul_distrib]
              rw [← Fintype.prod_sum (fun r (b : Bool) => (if b then pc else 1 - pc) * χ r b)]
              refine Finset.prod_congr rfl fun r _ => ?_
              simp [Fintype.sum_bool]
            have H4 : ∀ (σ : SSATPolicy φ.n) (r : Fin φ.n → Bool),
                σ.assign (fun v => !(if IsRandomVar v.val then !(r v) else true)) = σ.assign r := by
              intro σ r
              funext v
              unfold SSATPolicy.assign
              split_ifs with h hv
              · simp [hv]
              · congr 1; funext j; by_cases hj : IsRandomVar j.1.1 <;> simp [hj]
              · rfl
            have H5 : ∀ u, Plit u ≠ 0 → ∀ v : Fin φ.n, ¬ IsRandomVar v.val → u v = true := by
              intro u hu v hv
              by_contra hc
              apply hu
              refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
              simp [pl, hv, hc]
            have H6 : (∀ u, 0 ≤ Plit u) ∧ (∀ c, 0 ≤ Pcl c) ∧ ∑ c, Pcl c = 1 := by
              refine ⟨fun u => Finset.prod_nonneg fun v _ => ?_, fun c => Finset.prod_nonneg fun r _ => ?_, ?_⟩
              · simp only [pl]; split_ifs <;> norm_num
              · split_ifs <;> linarith
              · have := H3 (fun _ _ => 1)
                simp only [Finset.prod_const_one, mul_one] at this
                rw [this]; simp
            have H2 : ∀ H : (Fin φ.n → Bool) → ℝ, ∑ u, Plit u * H u =
                (∑ r : Fin φ.n → Bool, H (fun v => if IsRandomVar v.val then !(r v) else true)) / 2 ^ φ.n := by
              intro H
              let ψ : (Fin φ.n → Bool) → (Fin φ.n → Bool) := fun r v => if IsRandomVar v.val then !(r v) else true
              have e1 : ∀ r, H (ψ r) = ∑ u, (if ψ r = u then H u else 0) := by
                intro r; rw [Finset.sum_ite_eq]; simp
              have e2 : ∀ r u, (if ψ r = u then H u else 0) = H u * ∏ v, (if ψ r v = u v then (1:ℝ) else 0) := by
                intro r u
                rw [Finset.prod_boole]
                by_cases h : ψ r = u
                · simp [h]
                · simp only [h, if_false, Finset.mem_univ, true_implies]
                  rw [if_neg (fun h' => h (funext h'))]; simp
              have e3 : ∀ u, ∑ r : Fin φ.n → Bool, ∏ v, (if ψ r v = u v then (1:ℝ) else 0) = 2 ^ φ.n * Plit u := by
                intro u
                have := Fintype.prod_sum (fun v (b : Bool) => if (if IsRandomVar v.val then !b else true) = u v then (1:ℝ) else 0)
                simp only [ψ]
                rw [← this]
                simp only [Plit, pl]
                rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
                refine Finset.prod_congr rfl fun v _ => ?_
                by_cases hv : IsRandomVar v.val <;> cases u v <;> simp [hv, Fintype.sum_bool] <;> norm_num
              calc ∑ u, Plit u * H u = (∑ u, H u * (2 ^ φ.n * Plit u)) / 2 ^ φ.n := by
                    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun u _ => ?_; field_simp
                _ = (∑ u, H u * ∑ r : Fin φ.n → Bool, ∏ v, (if ψ r v = u v then (1:ℝ) else 0)) / 2 ^ φ.n := by
                    simp only [e3]
                _ = _ := by
                    congr 1
                    simp only [Finset.mul_sum]
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun r _ => ?_
                    rw [e1]
                    exact Finset.sum_congr rfl fun u _ => (e2 r u).symm
            have C2 : ∃ π', Lit π' = Elit ∧
                (1 - ((φ.clauses.length : ℝ) ^ 4)⁻¹) ^ (φ.clauses.length - 1) / (2 * k) * ssatOpt φ
                  ≤ clauseGain φ k π' := by
              obtain ⟨σs, hσs⟩ : ∃ σ : SSATPolicy φ.n, ssatValue φ σ = ssatOpt φ := by
                have : Finite (SSATPolicy φ.n) := by unfold SSATPolicy; infer_instance
                have : Nonempty (SSATPolicy φ.n) := ⟨fun _ _ => true⟩
                exact exists_eq_ciSup_of_finite
              let coin : (t : Fin (φ.n + φ.clauses.length)) →
                  ({s : Fin (φ.n + φ.clauses.length) // s ≤ t} → Bool) → Fin φ.n → Bool :=
                fun t pre w => if h : w.val ≤ t.val then
                  !(pre ⟨⟨w.val, by have := w.isLt; omega⟩, h⟩) else false
              let xs := fun t pre => σs.assign (coin t pre)
              let πs : OnlinePolicy (LitBin φ.n) (φ.n + φ.clauses.length) := fun t pre =>
                if ht : t.val < φ.n then
                  some (⟨t.val, ht⟩, if IsRandomVar t.val then true else !(xs t pre t.val))
                else ((φ.clauses.getD (t.val - φ.n) []).find?
                    (fun l => decide (l.1 < φ.n) && (xs t pre l.1 == l.2))).bind
                  (fun l => if h : l.1 < φ.n then some (⟨l.1, h⟩, l.2) else none)
              let X : (Fin (φ.n + φ.clauses.length) → Bool) → ℕ → Bool := fun a =>
                σs.assign (fun w => !(a (Fin.castAdd _ w)))
              have assign_dep : ∀ (r r' : Fin φ.n → Bool) (v : ℕ),
                  (∀ w : Fin φ.n, w.val ≤ v → r w = r' w) → σs.assign r v = σs.assign r' v := by
                intro r r' v h
                unfold SSATPolicy.assign
                split_ifs with hv hr
                · exact h _ le_rfl
                · congr 1; funext j
                  split_ifs
                  · exact h _ (by have := j.2; rw [Fin.lt_def] at this; simp at this; omega)
                  · rfl
                · rfl
              have hx_lit : ∀ (a : Fin (φ.n + φ.clauses.length) → Bool) (t : Fin (φ.n + φ.clauses.length)),
                  xs t (fun s => a s.1) t.val = X a t.val := by
                intro a t
                refine assign_dep _ _ _ fun w hw => ?_
                simp only [coin, dif_pos hw]; rfl
              have hx_cl : ∀ (a : Fin (φ.n + φ.clauses.length) → Bool) (t : Fin (φ.n + φ.clauses.length)),
                  φ.n ≤ t.val → xs t (fun s => a s.1) = X a := by
                intro a t ht
                simp only [xs, X]; congr 1; funext w
                have hw : w.val ≤ t.val := by have := w.isLt; omega
                simp only [coin, dif_pos hw]; rfl
              let bv : (Fin (φ.n + φ.clauses.length) → Bool) → Fin φ.n → Bool := fun a v =>
                if IsRandomVar v.val then true else !(X a v.val)
              have hMn : ∀ a j, j ≤ φ.n → πs.matchingUpTo a j =
                  (Finset.univ.filter (fun v : Fin φ.n => v.val < j ∧ a (Fin.castAdd _ v) = true)).image
                    (fun v => ((v, bv a v), Fin.castAdd _ v)) := by
                intro a j
                induction j with
                | zero => intro _; simp [OnlinePolicy.matchingUpTo]
                | succ j ih =>
                  intro hj
                  have hjn : j < φ.n := by omega
                  have hjN : j < φ.n + φ.clauses.length := by omega
                  have hπj : πs ⟨j, hjN⟩ (fun s => a s.1) = some ((⟨j, hjn⟩, bv a ⟨j, hjn⟩)) := by
                    simp only [πs, dif_pos hjn, bv]
                    congr 3
                    rw [hx_lit a ⟨j, hjN⟩]
                  simp only [OnlinePolicy.matchingUpTo]
                  rw [dif_pos hjN, hπj]
                  dsimp only
                  by_cases ha : a ⟨j, hjN⟩ = true
                  · have hfree : ∀ s, ((⟨j, hjn⟩, bv a ⟨j, hjn⟩), s) ∉ πs.matchingUpTo a j := by
                      intro s hs
                      rw [ih (by omega)] at hs
                      obtain ⟨v, hv, hve⟩ := Finset.mem_image.1 hs
                      have h1 := (Finset.mem_filter.1 hv).2.1
                      have h2 := congrArg (fun e => e.1.1.val) hve
                      simp at h2; omega
                    rw [if_pos ⟨ha, hfree⟩, ih (by omega)]
                    have hfe : (Finset.univ.filter (fun v : Fin φ.n => v.val < j + 1 ∧ a (Fin.castAdd _ v) = true))
                        = insert ⟨j, hjn⟩ (Finset.univ.filter (fun v : Fin φ.n => v.val < j ∧ a (Fin.castAdd _ v) = true)) := by
                      ext v
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
                      constructor
                      · rintro ⟨h1, h2⟩
                        by_cases hv : v.val = j
                        · left; exact hv
                        · right; exact ⟨by omega, h2⟩
                      · rintro (hv | ⟨h1, h2⟩)
                        · refine ⟨by omega, ?_⟩
                          have : v = ⟨j, hjn⟩ := Fin.ext hv
                          subst this; exact ha
                        · exact ⟨by omega, h2⟩
                    rw [hfe, Finset.image_insert]
                    congr 1
                    congr 1
                    exact Subsingleton.elim _ _
                  · rw [if_neg (by simp [ha]), ih (by omega)]
                    congr 1
                    ext v
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    constructor
                    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
                    · rintro ⟨h1, h2⟩
                      refine ⟨?_, h2⟩
                      by_contra hv
                      have : v = ⟨j, hjn⟩ := Fin.ext (show v.val = j by omega)
                      subst this; exact ha h2
              have hfilt : ∀ a j, (πs.matchingUpTo a (φ.n + j)).filter (fun e => ¬ φ.n ≤ e.2.val)
                  = πs.matchingUpTo a φ.n := by
                intro a j
                induction j with
                | zero =>
                  exact Finset.filter_true_of_mem (fun e he => by have := (G1 _ _ _ e he).1; omega)
                | succ j ih =>
                  ext e
                  simp only [Finset.mem_filter]
                  constructor
                  · rintro ⟨he, hl⟩
                    rcases Gcase πs a (φ.n + j) e he with h | h
                    · rw [← ih]; exact Finset.mem_filter.2 ⟨h, hl⟩
                    · omega
                  · intro he
                    rw [← ih] at he
                    obtain ⟨he, hl⟩ := Finset.mem_filter.1 he
                    exact ⟨Gsub _ _ _ he, hl⟩
              have hw1 : ∀ a (v : Fin φ.n), (gadget φ k).w (v, bv a v) (Fin.castAdd _ v) = 1 := by
                intro a v
                simp only [gadget, Fin.val_castAdd]
                rw [if_pos v.isLt]
                split_ifs with hc
                · rfl
                · exfalso; apply hc
                  simp only [bv]
                  by_cases h : IsRandomVar v.val
                  · exact ⟨trivial, Or.inr (by simp [h])⟩
                  · exact ⟨trivial, Or.inl h⟩
              have hLit : Lit πs = Elit := by
                simp only [Lit, Elit]
                refine Finset.sum_congr rfl fun a _ => ?_
                congr 1
                rw [show πs.matching a = πs.matchingUpTo a (φ.n + φ.clauses.length) from rfl, hfilt a _,
                  hMn a _ le_rfl, Finset.sum_image (fun v _ v' _ h => by
                    have := congrArg (fun e => e.1.1) h; simpa using this)]
                rw [Finset.sum_congr rfl (fun v _ => hw1 a v)]
                simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
                congr 1
                refine Finset.card_bij (fun v _ => Fin.castAdd _ v) ?_ ?_ ?_
                · intro v hv
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
                  exact ⟨by simp, hv.2⟩
                · intro v _ v' _ h; exact Fin.castAdd_injective _ _ h
                · intro t ht
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
                  refine ⟨⟨t.val, ht.1⟩, ?_, rfl⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨ht.1, ht.2⟩
              have hstay : ∀ a j (hj : j < φ.n + φ.clauses.length), a ⟨j, hj⟩ = false →
                  πs.matchingUpTo a (j + 1) = πs.matchingUpTo a j := by
                intro a j hj ha
                simp only [OnlinePolicy.matchingUpTo]
                rw [dif_pos hj]
                split
                · rw [if_neg (by simp [ha])]
                · rfl
              have hpre_n : ∀ a (r : Fin φ.clauses.length),
                  (∀ r' : Fin φ.clauses.length, r'.val < r.val → a (Fin.natAdd _ r') = false) →
                  πs.matchingUpTo a (φ.n + r.val) = πs.matchingUpTo a φ.n := by
                intro a r hr
                have : ∀ j, j ≤ r.val → πs.matchingUpTo a (φ.n + j) = πs.matchingUpTo a φ.n := by
                  intro j
                  induction j with
                  | zero => intro _; rfl
                  | succ j ih =>
                    intro hj
                    rw [← ih (by omega)]
                    exact hstay a (φ.n + j) (by omega) (hr ⟨j, by omega⟩ (by simp; omega))
                exact this _ le_rfl
              have hπcl : ∀ a (t : Fin (φ.n + φ.clauses.length)) (ht : φ.n ≤ t.val),
                  πs t (fun s => a s.1) = ((φ.clauses.getD (t.val - φ.n) []).find?
                    (fun l => decide (l.1 < φ.n) && (X a l.1 == l.2))).bind
                    (fun l => if h : l.1 < φ.n then some (⟨l.1, h⟩, l.2) else none) := by
                intro a t ht
                simp only [πs, dif_neg (by omega : ¬ t.val < φ.n)]
                rw [hx_cl a t ht]
              have hcl : ∀ a (r : Fin φ.clauses.length), a (Fin.natAdd _ r) = true →
                  (∀ r', r' ≠ r → a (Fin.natAdd _ r') = false) →
                  clauseSat (X a) (φ.clauses.getD r.val []) = true →
                  (φ.clauses.length : ℝ) ^ 4 / (2 * k) ≤
                    ∑ e ∈ (πs.matching a).filter (fun e => φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2 := by
                intro a r har hoth hsat
                have hCmem : φ.clauses.getD r.val [] ∈ φ.clauses := by
                  rw [List.getD_eq_getElem _ _ r.isLt]; exact List.getElem_mem _
                unfold clauseSat at hsat
                obtain ⟨l, hlC, hl⟩ := List.any_eq_true.1 hsat
                have hlt := (hφ _ hCmem).2.2 l hlC
                obtain ⟨l0, hl0⟩ : ∃ l0, (φ.clauses.getD r.val []).find?
                    (fun l => decide (l.1 < φ.n) && (X a l.1 == l.2)) = some l0 :=
                  Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨l, hlC, by simp [hlt]; simpa using hl⟩)
                have hp0 := List.find?_some hl0
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp0
                obtain ⟨h0, hX0⟩ := hp0
                have hl0C := List.mem_of_find?_eq_some hl0
                have hrN : φ.n + r.val < φ.n + φ.clauses.length := by omega
                have hπ : πs ⟨φ.n + r.val, hrN⟩ (fun s => a s.1) = some (⟨l0.1, h0⟩, l0.2) := by
                  rw [hπcl a _ (by simp)]
                  simp only [Nat.add_sub_cancel_left]
                  rw [hl0]
                  simp [h0]
                have hM : πs.matchingUpTo a (φ.n + r.val) = πs.matchingUpTo a φ.n :=
                  hpre_n a r (fun r' hr' => hoth r' (fun h => by subst h; omega))
                have hfree : ∀ s, ((⟨l0.1, h0⟩, l0.2), s) ∉ πs.matchingUpTo a (φ.n + r.val) := by
                  intro s hs
                  rw [hM, hMn a _ le_rfl] at hs
                  obtain ⟨v, hv, hve⟩ := Finset.mem_image.1 hs
                  have hav := (Finset.mem_filter.1 hv).2.2
                  have e1 : v.val = l0.1 := congrArg (fun e => e.1.1.val) hve
                  have e2 : bv a v = l0.2 := congrArg (fun e => e.1.2) hve
                  simp only [bv] at e2
                  by_cases hr : IsRandomVar v.val
                  · rw [if_pos hr] at e2
                    have hXv : X a v.val = !(a (Fin.castAdd _ v)) := by
                      simp only [X, SSATPolicy.assign, dif_pos v.isLt, if_pos hr]
                    rw [e1, hX0, ← e2, hav] at hXv
                    simp at hXv
                  · rw [if_neg hr, e1, hX0] at e2
                    cases h : l0.2 <;> simp [h] at e2
                have hin : ((⟨l0.1, h0⟩, l0.2), Fin.natAdd φ.n r) ∈ πs.matchingUpTo a (φ.n + r.val + 1) := by
                  simp only [OnlinePolicy.matchingUpTo]
                  rw [dif_pos hrN, hπ]
                  dsimp only
                  rw [if_pos ⟨har, hfree⟩]
                  have memself : ∀ {α : Type} {inst : DecidableEq α} (x : α) (s : Finset α),
                      x ∈ @insert _ _ (@Finset.instInsert _ inst) x s := by
                    intro α inst x s; exact Finset.mem_insert_self x s
                  exact memself _ _
                have hinN : ((⟨l0.1, h0⟩, l0.2), Fin.natAdd φ.n r) ∈ πs.matching a :=
                  Gmono _ _ _ _ (by omega) hin
                have hw : (gadget φ k).w (⟨l0.1, h0⟩, l0.2) (Fin.natAdd φ.n r) =
                    (φ.clauses.length : ℝ) ^ 4 / (2 * k) := by
                  simp only [gadget, Fin.val_natAdd]
                  rw [if_neg (by omega), if_pos]
                  simpa using hl0C
                have hmem : ((⟨l0.1, h0⟩, l0.2), Fin.natAdd φ.n r) ∈
                    (πs.matching a).filter (fun e => φ.n ≤ e.2.val) :=
                  Finset.mem_filter.2 ⟨hinN, by simp only [Fin.val_natAdd]; omega⟩
                rw [← hw]
                exact Finset.single_le_sum (f := fun e => (gadget φ k).w e.1 e.2)
                  (fun e _ => (gadget φ k).w_nonneg _ _) hmem
              let χ : Fin φ.clauses.length → Fin φ.clauses.length → Bool → ℝ := fun r r' b =>
                if r' = r then (if b then 1 else 0) else (if b then 0 else 1)
              let sat : (ℕ → Bool) → Fin φ.clauses.length → ℝ := fun x r =>
                if clauseSat x (φ.clauses.getD r.val []) then 1 else 0
              let W : ℝ := (φ.clauses.length : ℝ) ^ 4 / (2 * k)
              have hP0 : ∀ a, 0 ≤ arrivalProb (gadget φ k) a := by
                intro a; unfold arrivalProb
                exact Finset.prod_nonneg fun t _ => by
                  have := (gadget φ k).p_nonneg t; have := (gadget φ k).p_le_one t
                  split_ifs <;> linarith
              have hcp0 : ∀ a, 0 ≤ ∑ e ∈ (πs.matching a).filter (fun e => φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2 :=
                fun a => Finset.sum_nonneg fun e _ => (gadget φ k).w_nonneg _ _
              have hpt : ∀ a, ∑ r, W * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r'))) ≤
                  ∑ e ∈ (πs.matching a).filter (fun e => φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2 := by
                intro a
                by_cases hex : ∃ r, a (Fin.natAdd _ r) = true ∧ ∀ r', r' ≠ r → a (Fin.natAdd _ r') = false
                · obtain ⟨r0, h0, h0'⟩ := hex
                  rw [Finset.sum_eq_single r0]
                  · have hQ : ∏ r', χ r0 r' (a (Fin.natAdd _ r')) = 1 := Finset.prod_eq_one fun r' _ => by
                      simp only [χ]
                      by_cases h : r' = r0
                      · subst h; simp [h0]
                      · simp [h, h0' r' h]
                    rw [hQ, mul_one]
                    simp only [sat]
                    split_ifs with hs
                    · rw [mul_one]; exact hcl a r0 h0 h0' hs
                    · rw [mul_zero]; exact hcp0 a
                  · intro r _ hr
                    have : ∏ r', χ r r' (a (Fin.natAdd _ r')) = 0 :=
                      Finset.prod_eq_zero (Finset.mem_univ r) (by simp only [χ, if_pos rfl]; simp [h0' r hr])
                    rw [this]; simp
                  · intro h; exact absurd (Finset.mem_univ _) h
                · rw [Finset.sum_eq_zero]
                  · exact hcp0 a
                  intro r _
                  have : ∏ r', χ r r' (a (Fin.natAdd _ r')) = 0 := by
                    by_cases hr : a (Fin.natAdd _ r) = true
                    · push_neg at hex
                      obtain ⟨r', hr', hr'a⟩ := hex r hr
                      have : a (Fin.natAdd _ r') = true := by simpa using hr'a
                      exact Finset.prod_eq_zero (Finset.mem_univ r') (by simp only [χ, if_neg hr']; simp [this])
                    · exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp only [χ, if_pos rfl]; simp [hr])
                  rw [this]; simp
              have hQsum : ∀ r, ∑ c, Pcl c * ∏ r', χ r r' (c r') = pc * (1 - pc) ^ (φ.clauses.length - 1) := by
                intro r
                rw [H3, Fintype.prod_eq_mul_prod_compl r]
                have hc : ∀ r' ∈ ({r}ᶜ : Finset (Fin φ.clauses.length)),
                    (pc * χ r r' true + (1 - pc) * χ r r' false) = 1 - pc := by
                  intro r' hr'
                  have : r' ≠ r := by simpa using hr'
                  simp [χ, this]
                rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_compl, Finset.card_singleton,
                  Fintype.card_fin]
                simp [χ]
              have hlist : ∀ (x : ℕ → Bool) (L : List (List (ℕ × Bool))),
                  ((L.countP (clauseSat x) : ℕ) : ℝ) =
                    ∑ i ∈ Finset.range L.length, if clauseSat x (L.getD i []) then (1 : ℝ) else 0 := by
                intro x L
                induction L with
                | nil => simp
                | cons C L ih =>
                  rw [List.countP_cons, List.length_cons, Finset.sum_range_succ']
                  simp only [List.getD_cons_zero, List.getD_cons_succ]
                  push_cast
                  rw [ih]
                  try (split_ifs <;> simp)
              have hsatsum : ∀ x, ∑ r, sat x r = (φ.numSat x : ℝ) := by
                intro x
                simp only [sat, SSATFormula.numSat]
                rw [hlist, Fin.sum_univ_eq_sum_range (fun i => if clauseSat x (φ.clauses.getD i []) then (1 : ℝ) else 0)]
              have hE : ∀ r, ∑ a, arrivalProb (gadget φ k) a * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r')))
                  = ((∑ ρ : Fin φ.n → Bool, sat (σs.assign ρ) r) / 2 ^ φ.n) * (pc * (1 - pc) ^ (φ.clauses.length - 1)) := by
                intro r
                rw [H1]
                simp only [X, Fin.append_left, Fin.append_right]
                rw [← hQsum r]
                have := H2 (fun u => sat (σs.assign fun w => !u w) r)
                simp only [H4] at this
                rw [← this, Finset.sum_mul_sum]
                refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun c _ => ?_
                ring
              have hmain : ∑ a, arrivalProb (gadget φ k) a *
                  ∑ r, W * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r')))
                  = W * (pc * (1 - pc) ^ (φ.clauses.length - 1)) * ssatValue φ σs := by
                rw [show (∑ a, arrivalProb (gadget φ k) a *
                    ∑ r, W * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r')))) =
                    ∑ a, ∑ r, W * (arrivalProb (gadget φ k) a * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r'))))
                    from Finset.sum_congr rfl fun a _ => by
                      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring]
                rw [Finset.sum_comm]
                simp_rw [← Finset.mul_sum, hE]
                simp only [ssatValue]
                simp_rw [← hsatsum]
                rw [Finset.sum_comm (f := fun ρ r => sat (σs.assign ρ) r), Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun r _ => ?_
                ring
              have key : ∀ y : ℝ, W * (pc * y) = y / (2 * k) := by
                intro y
                have hm0 : (φ.clauses.length : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
                simp only [W, pc]
                field_simp
              refine ⟨πs, hLit, ?_⟩
              calc (1 - ((φ.clauses.length : ℝ) ^ 4)⁻¹) ^ (φ.clauses.length - 1) / (2 * k) * ssatOpt φ
                  = ∑ a, arrivalProb (gadget φ k) a *
                      ∑ r, W * (sat (X a) r * ∏ r', χ r r' (a (Fin.natAdd _ r'))) := by
                    rw [hmain, key, hσs]
                _ ≤ clauseGain φ k πs :=
                    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hP0 a)
            have C3 : clauseGain φ k π ≤ ssatOpt φ / (2 * k) + (Elit - Lit π) / 2 := by
              classical
              have hcount0 : ∀ (l : List (List (ℕ × Bool))) (p : List (ℕ × Bool) → Bool),
                  ((Finset.univ.filter (fun r : Fin l.length => p (l.get r) = true)).card : ℝ) = (l.countP p : ℝ) := by
                intro l p
                rw [Finset.card_filter]
                push_cast
                induction l with
                | nil => simp
                | cons x xs ih =>
                  change (∑ i : Fin (xs.length + 1), _) = _
                  rw [Fin.sum_univ_succ, List.countP_cons]
                  simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
                    List.getElem_cons_succ] at ih ⊢
                  rw [ih]; by_cases hx : p x = true <;> simp [hx] <;> ring
              have Gat : ∀ (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                  ∀ e ∈ π.matchingUpTo a j, e ∈ π.matchingUpTo a (e.2.val + 1) := by
                intro a j
                induction j with
                | zero => simp [OnlinePolicy.matchingUpTo]
                | succ j ih =>
                  intro e he
                  rcases Gcase π a j e he with h | h
                  · exact ih e h
                  · rw [h]; exact he
              have GP : ∀ (a : Fin (φ.n + φ.clauses.length) → Bool) (j : ℕ),
                  ∀ e ∈ π.matchingUpTo a j, π e.2 (fun s => a s.1) = some e.1 := by
                intro a j
                induction j with
                | zero => simp [OnlinePolicy.matchingUpTo]
                | succ j ih =>
                  intro e he
                  simp only [OnlinePolicy.matchingUpTo] at he
                  split_ifs at he with hj
                  · split at he
                    · rename_i i hi
                      split_ifs at he with hc
                      · rcases memins _ _ _ he with rfl | he
                        · exact hi
                        · exact ih e he
                      · exact ih e he
                    · exact ih e he
                  · exact ih e he
              let pre : (v : Fin φ.n) → ({j : Fin φ.n // j < v} → Bool) →
                  {s : Fin (φ.n + φ.clauses.length) // s ≤ ⟨v.val, Nat.lt_add_right _ v.isLt⟩} → Bool :=
                fun v f s => if h : s.1.val < v.val then
                  (if IsRandomVar s.1.val then !(f ⟨⟨s.1.val, h.trans v.isLt⟩, h⟩) else true) else true
              let σπ : SSATPolicy φ.n := fun v f =>
                match π ⟨v.val, Nat.lt_add_right _ v.isLt⟩ (pre v f) with
                | some i => if i.1 = v then !i.2 else true
                | none => true
              have KF : ∀ a : Fin (φ.n + φ.clauses.length) → Bool,
                  (∀ v : Fin φ.n, ¬ IsRandomVar v.val → a (Fin.castAdd φ.clauses.length v) = true) →
                  ∀ v : Fin φ.n, ¬ IsRandomVar v.val → ∀ i,
                    π ⟨v.val, Nat.lt_add_right _ v.isLt⟩ (fun s => a s.1) = some i →
                    σπ.assign (fun w => !a (Fin.castAdd φ.clauses.length w)) v.val = if i.1 = v then !i.2 else true := by
                intro a hdet v hv i hi
                have hpre : pre v (fun j => if IsRandomVar j.1.1 then
                    (fun w => !a (Fin.castAdd φ.clauses.length w)) j.1 else false) = fun s => a s.1 := by
                  funext s
                  rcases s with ⟨⟨s, hs⟩, hsv⟩
                  simp only [pre]
                  by_cases h' : s < v.val
                  · rw [dif_pos h']
                    by_cases hr : IsRandomVar s
                    · rw [if_pos hr, if_pos hr, Bool.not_not]; rfl
                    · rw [if_neg hr]; exact (hdet ⟨s, h'.trans v.isLt⟩ hr).symm
                  · rw [dif_neg h']
                    have : s = v.val := by
                      have := Fin.le_def.1 hsv; simp at this; omega
                    subst this
                    exact (hdet v hv).symm
                unfold SSATPolicy.assign
                rw [dif_pos v.isLt, if_neg hv]
                simp only [σπ, Fin.eta]
                rw [hpre, hi]
              let FreeC : (Fin (φ.n + φ.clauses.length) → Bool) → Fin φ.clauses.length → Prop := fun a r =>
                ∃ l ∈ φ.clauses.get r, ∃ hl : l.1 < φ.n, ∀ s, ((⟨l.1, hl⟩, l.2), s) ∉ π.matchingUpTo a φ.n
              let W : ℝ := (φ.clauses.length : ℝ) ^ 4 / (2 * k)
              have hW0 : 0 ≤ W := by positivity
              have A3 : ∀ a, ∑ e ∈ (π.matching a).filter (fun e => φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2
                  ≤ ∑ r : Fin φ.clauses.length, (if a (Fin.natAdd φ.n r) = true then (1:ℝ) else 0) *
                      (if FreeC a r then W else 0) := by
                intro a
                rw [← Finset.sum_fiberwise _ (fun e : LitBin φ.n × Fin (φ.n + φ.clauses.length) => e.2),
                  Fin.sum_univ_add]
                have hz : ∑ v : Fin φ.n, ∑ e ∈ ((π.matching a).filter (fun e => φ.n ≤ e.2.val)).filter
                    (fun e => e.2 = Fin.castAdd φ.clauses.length v), (gadget φ k).w e.1 e.2 = 0 := by
                  refine Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun e he => ?_
                  have he1 := (Finset.mem_filter.1 he).2
                  have he2 := (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).2
                  rw [he1, Fin.val_castAdd] at he2
                  exact absurd v.isLt (by omega)
                rw [hz, zero_add]
                refine Finset.sum_le_sum fun r _ => ?_
                have hRnn : 0 ≤ (if a (Fin.natAdd φ.n r) = true then (1:ℝ) else 0) * (if FreeC a r then W else 0) := by
                  split_ifs <;> simp [hW0]
                rcases (((π.matching a).filter (fun e => φ.n ≤ e.2.val)).filter
                    (fun e => e.2 = Fin.natAdd φ.n r)).eq_empty_or_nonempty with hT0 | ⟨e0, he0⟩
                · rw [hT0, Finset.sum_empty]; exact hRnn
                · have he0' := Finset.mem_filter.1 he0
                  have he0M : e0 ∈ π.matchingUpTo a (φ.n + φ.clauses.length) := (Finset.mem_filter.1 he0'.1).1
                  have hsub : ((π.matching a).filter (fun e => φ.n ≤ e.2.val)).filter
                      (fun e => e.2 = Fin.natAdd φ.n r) ⊆ {e0} := by
                    intro e he
                    have he' := Finset.mem_filter.1 he
                    rw [Finset.mem_singleton]
                    exact Gball π a _ e (Finset.mem_filter.1 he'.1).1 e0 he0M (he'.2.trans he0'.2.symm)
                  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
                    (fun _ _ _ => (gadget φ k).w_nonneg _ _)).trans ?_
                  rw [Finset.sum_singleton]
                  have hw : (gadget φ k).w e0.1 e0.2 =
                      if (e0.1.1.val, e0.1.2) ∈ φ.clauses.get r then W else 0 := by
                    simp only [gadget, he0'.2, Fin.val_natAdd]
                    rw [if_neg (by omega)]
                    simp [W]
                  rw [hw]
                  by_cases hin : (e0.1.1.val, e0.1.2) ∈ φ.clauses.get r
                  · rw [if_pos hin]
                    have ha : a (Fin.natAdd φ.n r) = true := by
                      rw [← he0'.2]; exact (G1 π a _ e0 he0M).2
                    have hF : FreeC a r := ⟨_, hin, e0.1.1.isLt, fun s hs =>
                      Gfree π a _ e0 he0M s (Gmono π a _ _ (by rw [he0'.2]; simp) hs)⟩
                    rw [if_pos ha, if_pos hF, one_mul]
                  · rw [if_neg hin]; exact hRnn
              have Ind : ∀ Fa : (Fin (φ.n + φ.clauses.length) → Bool) → Fin φ.clauses.length → ℝ,
                  (∀ u c c' r, Fa (Fin.append u c) r = Fa (Fin.append u c') r) →
                  ∑ a, arrivalProb (gadget φ k) a * ∑ r, (if a (Fin.natAdd φ.n r) = true then (1:ℝ) else 0) * Fa a r
                    = pc * ∑ a, arrivalProb (gadget φ k) a * ∑ r, Fa a r := by
                intro Fa hFa
                have hind : ∀ r, ∑ c, Pcl c * (if c r = true then (1:ℝ) else 0) = pc := by
                  intro r
                  let χ : Fin φ.clauses.length → Bool → ℝ := fun r' b => if r' = r then (if b = true then (1:ℝ) else 0) else 1
                  have e1 : ∀ c : Fin φ.clauses.length → Bool, ∏ r', χ r' (c r') = if c r = true then 1 else 0 := by
                    intro c
                    rw [Finset.prod_eq_single r]
                    · simp [χ]
                    · intro b _ hb; simp [χ, hb]
                    · intro h; exact absurd (Finset.mem_univ r) h
                  have e2 : ∏ r', (pc * χ r' true + (1 - pc) * χ r' false) = pc := by
                    rw [Finset.prod_eq_single r]
                    · simp [χ]
                    · intro b _ hb; simp [χ, hb]
                    · intro h; exact absurd (Finset.mem_univ r) h
                  calc ∑ c, Pcl c * (if c r = true then (1:ℝ) else 0) = ∑ c, Pcl c * ∏ r', χ r' (c r') :=
                        Finset.sum_congr rfl fun c _ => by rw [e1 c]
                    _ = _ := H3 χ
                    _ = pc := e2
                rw [H1, H1, Finset.mul_sum]
                refine Finset.sum_congr rfl fun u _ => ?_
                obtain ⟨g, hg⟩ : ∃ g : Fin φ.clauses.length → ℝ, ∀ c r, Fa (Fin.append u c) r = g r :=
                  ⟨_, fun c r => hFa u c (fun _ => false) r⟩
                simp only [Fin.append_right, hg]
                calc ∑ c, Plit u * Pcl c * ∑ r, (if c r = true then (1:ℝ) else 0) * g r
                    = ∑ r, Plit u * g r * ∑ c, Pcl c * (if c r = true then (1:ℝ) else 0) := by
                      simp only [Finset.mul_sum]; rw [Finset.sum_comm]
                      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => by ring
                  _ = ∑ r, Plit u * g r * pc := by simp only [hind]
                  _ = pc * ∑ c, Plit u * Pcl c * ∑ r, g r := by
                      have : ∑ c, Plit u * Pcl c * ∑ r, g r = (∑ c, Pcl c) * (Plit u * ∑ r, g r) := by
                        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
                      rw [this, H6.2.2, one_mul, Finset.mul_sum, Finset.mul_sum]
                      exact Finset.sum_congr rfl fun r _ => by ring
              have hFind : ∀ u c c' r, (if FreeC (Fin.append u c) r then W else 0) =
                  (if FreeC (Fin.append u c') r then W else 0) := by
                intro u c c' r
                have hM : π.matchingUpTo (Fin.append u c) φ.n = π.matchingUpTo (Fin.append u c') φ.n := by
                  apply Gpre
                  intro s hs
                  have : s = Fin.castAdd φ.clauses.length ⟨s.val, hs⟩ := Fin.ext rfl
                  rw [this, Fin.append_left, Fin.append_left]
                have : FreeC (Fin.append u c) r ↔ FreeC (Fin.append u c') r := by
                  simp only [FreeC, hM]
                by_cases h : FreeC (Fin.append u c) r
                · rw [if_pos h, if_pos (this.1 h)]
                · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]
              have hP0 : ∀ a, 0 ≤ arrivalProb (gadget φ k) a := fun a => Finset.prod_nonneg fun t _ => by
                have := (gadget φ k).p_nonneg t; have := (gadget φ k).p_le_one t
                split_ifs <;> linarith
              have hPdet : ∀ a, arrivalProb (gadget φ k) a ≠ 0 → ∀ v : Fin φ.n, ¬ IsRandomVar v.val →
                  a (Fin.castAdd φ.clauses.length v) = true := by
                intro a ha v hv
                by_contra hc
                apply ha
                refine Finset.prod_eq_zero (Finset.mem_univ (Fin.castAdd φ.clauses.length v)) ?_
                rw [if_neg hc]
                simp only [gadget, Fin.val_castAdd, if_pos v.isLt, if_neg hv]
                ring
              have hk : (1:ℝ) ≤ k := by exact_mod_cast hk1
              have hm : (1:ℝ) ≤ φ.clauses.length := by exact_mod_cast hm1
              have hW : W * pc = 1 / (2 * k) := by
                simp only [W, pc]; field_simp
              have B3 : ∀ a : Fin (φ.n + φ.clauses.length) → Bool,
                  (∀ v : Fin φ.n, ¬ IsRandomVar v.val → a (Fin.castAdd φ.clauses.length v) = true) →
                  ((Finset.univ.filter (fun r => FreeC a r)).card : ℝ) ≤
                    (φ.numSat (σπ.assign (fun w => !a (Fin.castAdd φ.clauses.length w))) : ℝ) +
                    k * (((Finset.univ.filter (fun t : Fin (φ.n + φ.clauses.length) => t.val < φ.n ∧ a t = true)).card : ℝ) -
                      ∑ e ∈ (π.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2) := by
                intro a hdet
                set X := σπ.assign (fun w => !a (Fin.castAdd φ.clauses.length w)) with hX
                have hwlit : ∀ (i : LitBin φ.n) (t : Fin (φ.n + φ.clauses.length)), t.val < φ.n →
                    (gadget φ k).w i t = if i.1.val = t.val ∧ (¬ IsRandomVar t.val ∨ i.2 = true) then 1 else 0 := by
                  intro i t ht
                  simp only [gadget]; rw [if_pos ht]
                let Q : Fin (φ.n + φ.clauses.length) → Prop := fun t =>
                  ∃ e ∈ π.matching a, e.2 = t ∧ (gadget φ k).w e.1 e.2 = 1
                set Arr := Finset.univ.filter (fun t : Fin (φ.n + φ.clauses.length) => t.val < φ.n ∧ a t = true)
                have hArr : Arr.card = (Arr.filter Q).card + (Arr.filter (fun t => ¬ Q t)).card :=
                  (Finset.card_filter_add_card_filter_not Q).symm
                have hLw : ∑ e ∈ (π.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2
                    ≤ ((Arr.filter Q).card : ℝ) := by
                  have h01 : ∀ e ∈ (π.matching a).filter (fun e => ¬ φ.n ≤ e.2.val),
                      (gadget φ k).w e.1 e.2 = if (gadget φ k).w e.1 e.2 = 1 then 1 else 0 := by
                    intro e he
                    have := (Finset.mem_filter.1 he).2
                    rw [hwlit _ _ (by omega)]
                    by_cases hc : e.1.1.val = e.2.val ∧ (¬ IsRandomVar e.2.val ∨ e.1.2 = true)
                    · rw [if_pos hc, if_pos rfl]
                    · rw [if_neg hc, if_neg (by norm_num : (0:ℝ) ≠ 1)]
                  rw [Finset.sum_congr rfl h01, Finset.sum_boole]
                  rw [← Finset.card_image_of_injOn (f := Prod.snd)]
                  · exact_mod_cast Finset.card_le_card (fun t ht => by
                      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
                      have hh := Finset.mem_filter.1 he
                      have hh1 := Finset.mem_filter.1 hh.1
                      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega,
                        (G1 π a _ e hh1.1).2⟩, e, hh1.1, rfl, hh.2⟩)
                  · intro e he e' he' hee
                    exact Gball π a _ e (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).1 e'
                      (Finset.mem_filter.1 (Finset.mem_filter.1 he').1).1 hee
                have hocc : ∀ v : ℕ, (Finset.univ.filter (fun r : Fin φ.clauses.length =>
                    (φ.clauses.get r).any (fun l => l.1 == v) = true)).card ≤ k := by
                  intro v
                  have hc := hcount0 φ.clauses (fun C => C.any fun l => l.1 == v)
                  have h' : ((Finset.univ.filter (fun r : Fin φ.clauses.length =>
                      (φ.clauses.get r).any (fun l => l.1 == v) = true)).card : ℝ) ≤ k := by
                    rw [hc, List.countP_eq_length_filter]; exact_mod_cast h2 v
                  exact_mod_cast h'
                have hinM : ∀ e ∈ π.matching a, e.2.val < φ.n → e ∈ π.matchingUpTo a φ.n := fun e he hlt =>
                  Gmono π a _ _ (by omega) (Gat a _ e he)
                have hsub : Finset.univ.filter (fun r => FreeC a r) ⊆
                    Finset.univ.filter (fun r : Fin φ.clauses.length => clauseSat X (φ.clauses.get r) = true) ∪
                    (Arr.filter (fun t => ¬ Q t)).biUnion (fun t => Finset.univ.filter (fun r : Fin φ.clauses.length =>
                      (φ.clauses.get r).any (fun l => l.1 == t.val) = true)) := by
                  intro r hr
                  obtain ⟨⟨lv, lb⟩, hl, hln, hfree⟩ := (Finset.mem_filter.1 hr).2
                  simp only at hln hfree
                  have htv : (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)).val = lv := rfl
                  have hanyl : (φ.clauses.get r).any
                      (fun l' => l'.1 == (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)).val) = true :=
                    List.any_eq_true.2 ⟨(lv, lb), hl, by rw [htv]; exact beq_self_eq_true lv⟩
                  by_cases hL : Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n) ∈ Arr.filter (fun t => ¬ Q t)
                  · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hL,
                      Finset.mem_filter.2 ⟨Finset.mem_univ _, hanyl⟩⟩)
                  · apply Finset.mem_union_left
                    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
                    have hQ : a (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)) = true →
                        Q (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)) := by
                      intro hat; by_contra hq
                      exact hL (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hln, hat⟩, hq⟩)
                    suffices hXl : X lv = lb by
                      show (φ.clauses.get r).any (fun l => X l.1 == l.2) = true
                      exact List.any_eq_true.2 ⟨(lv, lb), hl, by rw [hXl]; exact beq_self_eq_true lb⟩
                    by_cases hr : IsRandomVar lv
                    · have hl2 : lb = true := h1 _ (List.get_mem _ _) (lv, lb) hl hr
                      have hXv : X lv = !a (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)) := by
                        rw [hX]; unfold SSATPolicy.assign; rw [dif_pos hln, if_pos hr]
                      rw [hXv, hl2]
                      by_cases hat : a (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)) = true
                      · exfalso
                        obtain ⟨⟨⟨iv, ib⟩, e2⟩, heM, he2, hw1⟩ := hQ hat
                        simp only at he2 hw1
                        subst he2
                        rw [hwlit _ _ hln] at hw1
                        split_ifs at hw1 with hc
                        · simp only [htv] at hc
                          have hib : ib = true := hc.2.resolve_left (fun h => h hr)
                          have hiv : iv = ⟨lv, hln⟩ := Fin.ext hc.1
                          subst hib hiv hl2
                          exact hfree _ (hinM _ heM hln)
                        · exact absurd hw1 (by norm_num)
                      · rw [Bool.not_eq_true] at hat; rw [hat]; rfl
                    · have hat : a (Fin.castAdd φ.clauses.length (⟨lv, hln⟩ : Fin φ.n)) = true := hdet ⟨lv, hln⟩ hr
                      obtain ⟨⟨⟨iv, ib⟩, e2⟩, heM, he2, hw1⟩ := hQ hat
                      simp only at he2 hw1
                      subst he2
                      have hGP := GP a _ _ heM
                      have hK : X lv = _ := KF a hdet ⟨lv, hln⟩ hr (iv, ib) hGP
                      rw [hwlit _ _ hln] at hw1
                      split_ifs at hw1 with hc
                      · simp only [htv] at hc
                        have hiv : iv = ⟨lv, hln⟩ := Fin.ext hc.1
                        subst hiv
                        rw [hK, if_pos rfl]
                        have hne : ib ≠ lb := by
                          rintro rfl
                          exact hfree _ (hinM _ heM hln)
                        revert hne; cases ib <;> cases lb <;> simp
                      · exact absurd hw1 (by norm_num)
                have hN : (Finset.univ.filter (fun r => FreeC a r)).card ≤
                    (Finset.univ.filter (fun r : Fin φ.clauses.length => clauseSat X (φ.clauses.get r) = true)).card +
                      k * (Arr.filter (fun t => ¬ Q t)).card := by
                  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
                  refine Finset.card_biUnion_le.trans ?_
                  refine (Finset.sum_le_sum fun t _ => hocc t.val).trans ?_
                  rw [Finset.sum_const, smul_eq_mul, mul_comm]
                have hnsat : ((Finset.univ.filter (fun r : Fin φ.clauses.length =>
                    clauseSat X (φ.clauses.get r) = true)).card : ℝ) = (φ.numSat X : ℝ) := hcount0 φ.clauses (clauseSat X)
                have hNR : ((Finset.univ.filter (fun r => FreeC a r)).card : ℝ) ≤
                    (φ.numSat X : ℝ) + k * ((Arr.filter (fun t => ¬ Q t)).card : ℝ) := by
                  rw [← hnsat]; exact_mod_cast hN
                have hArrR : (Arr.card : ℝ) = ((Arr.filter Q).card : ℝ) + ((Arr.filter (fun t => ¬ Q t)).card : ℝ) := by
                  exact_mod_cast hArr
                have hk0 : (0:ℝ) ≤ k := by positivity
                nlinarith [mul_le_mul_of_nonneg_left hLw hk0]
              have hfin : Finite (SSATPolicy φ.n) := by unfold SSATPolicy; infer_instance
              have hS : ssatValue φ σπ ≤ ssatOpt φ := le_ciSup (Set.finite_range _).bddAbove σπ
              have hnum : ∑ a, arrivalProb (gadget φ k) a *
                  (φ.numSat (σπ.assign (fun w => !a (Fin.castAdd φ.clauses.length w))) : ℝ) = ssatValue φ σπ := by
                rw [H1]
                simp only [Fin.append_left]
                have : ∀ u, ∑ c, Plit u * Pcl c * (φ.numSat (σπ.assign (fun w => !u w)) : ℝ)
                    = Plit u * φ.numSat (σπ.assign (fun w => !u w)) := by
                  intro u; rw [← Finset.sum_mul, ← Finset.mul_sum, H6.2.2, mul_one]
                simp only [this]
                rw [H2]
                simp only [H4]
                rfl
              calc clauseGain φ k π
                  ≤ ∑ a, arrivalProb (gadget φ k) a * ∑ r, (if a (Fin.natAdd φ.n r) = true then (1:ℝ) else 0) *
                      (if FreeC a r then W else 0) := by
                    unfold clauseGain
                    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (A3 a) (hP0 a)
                _ = pc * ∑ a, arrivalProb (gadget φ k) a * ∑ r, (if FreeC a r then W else 0) :=
                    Ind (fun a r => if FreeC a r then W else 0) hFind
                _ = ∑ a, arrivalProb (gadget φ k) a *
                      ((1 / (2 * k)) * ((Finset.univ.filter (fun r => FreeC a r)).card : ℝ)) := by
                    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, ← hW]; ring
                _ ≤ ∑ a, arrivalProb (gadget φ k) a * ((1 / (2 * k)) *
                      ((φ.numSat (σπ.assign (fun w => !a (Fin.castAdd φ.clauses.length w))) : ℝ) +
                    k * (((Finset.univ.filter (fun t : Fin (φ.n + φ.clauses.length) => t.val < φ.n ∧ a t = true)).card : ℝ) -
                      ∑ e ∈ (π.matching a).filter (fun e => ¬ φ.n ≤ e.2.val), (gadget φ k).w e.1 e.2))) := by
                    refine Finset.sum_le_sum fun a _ => ?_
                    by_cases ha : arrivalProb (gadget φ k) a = 0
                    · rw [ha, zero_mul, zero_mul]
                    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (B3 a (hPdet a ha))
                        (by positivity)) (hP0 a)
                _ = ssatValue φ σπ / (2 * k) + (Elit - Lit π) / 2 := by
                    rw [← hnum]; simp only [Elit, Lit]
                    rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl fun a _ => ?_
                    field_simp
                _ ≤ _ := by gcongr
            have C4 : 0 ≤ ssatOpt φ ∧ ssatOpt φ ≤ φ.clauses.length := by
              have hfin : Finite (SSATPolicy φ.n) := by unfold SSATPolicy; infer_instance
              have hne : Nonempty (SSATPolicy φ.n) := ⟨fun _ _ => true⟩
              have hv : ∀ σ, 0 ≤ ssatValue φ σ ∧ ssatValue φ σ ≤ φ.clauses.length := by
                intro σ
                unfold ssatValue
                constructor
                · positivity
                · rw [div_le_iff₀ (by positivity)]
                  calc (∑ r : Fin φ.n → Bool, (φ.numSat (σ.assign r) : ℝ))
                      ≤ ∑ r : Fin φ.n → Bool, (φ.clauses.length : ℝ) := by
                        gcongr with r
                        exact_mod_cast List.countP_le_length
                    _ = _ := by simp [Finset.card_univ, mul_comm]
              obtain ⟨σ0⟩ := id hne
              exact ⟨le_ciSup_of_le (Set.finite_range _).bddAbove σ0 (hv σ0).1,
                ciSup_le fun σ => (hv σ).2⟩
            obtain ⟨π', hL', hB'⟩ := C2
            have hle := hopt π'
            rw [hsplit, hsplit] at hle
            obtain ⟨r1, r2⟩ := arith _ _ _ _ _ _ _ _ hm1 hk1 C4.1 C4.2 (C1 π) hL' hle hB' C3
            exact ⟨_, r1, r2, by ring⟩
