-- Prove2me | solution 1 for ShapeMoment.LogConcave.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:01.633639+00:00
-- url     : https://prove2.me/submissions/3328ae5d-7c3e-4ea0-8fa5-b20f8dcc54c1

import Definitions.Def_ShapeMoment_LogConcave_Supplement_IFRModel

open ShapeMoment
open ShapeMoment.LogConcave
open ShapeMoment.LogConcave.Supplement

theorem solution (n m : ℕ) (f : Fin n → ℝ) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hfeas : (feasIFRPrime n m q).Nonempty) :
    (∃ y ∈ (feasIFRPrime n m q).extremePoints ℝ,
      IsIFRMaxSol f (feasIFRPrime n m q) y) ∧
    ∀ y ∈ (feasIFRPrime n m q).extremePoints ℝ,
      IsIFRMaxSol f (feasIFRPrime n m q) y →
      ∃ (a k s : ℕ) (b : Fin (s + 1) → ℕ) (α r : Fin s → ℝ),
        1 ≤ a ∧ a ≤ k ∧ k ≤ n ∧ s ≤ m ∧
        (∀ j, 1 ≤ j → j ≤ a → ext y j = 1) ∧
        (∀ j, a ≤ j → j < k → ext y (j + 1) < ext y j) ∧
        (∀ j, 1 ≤ j → j ≤ k → 0 < ext y j) ∧
        (∀ j, k < j → ext y j = 0) ∧
        StrictMono b ∧ b 0 = a ∧ b (Fin.last s) = k ∧
        (∀ i, 0 < α i ∧ 0 < r i ∧ r i < 1) ∧
        (∀ i : Fin s, ∀ j, b i.castSucc ≤ j → j ≤ b i.succ →
          ext y j = α i * r i ^ (j - b i.castSucc)) := by
            classical
            have hextc : ∀ j, Continuous (fun y : Fin n → ℝ => ext y j) := by
              intro j; unfold ShapeMoment.LogConcave.ext; split_ifs <;> fun_prop
            have hextlin : ∀ (y z : Fin n → ℝ) (a b : ℝ) (j : ℕ),
                ext (a • y + b • z) j = a * ext y j + b * ext z j := by
              intro y z a b j; unfold ShapeMoment.LogConcave.ext; split_ifs <;> simp
            have hextval : ∀ (x : Fin n → ℝ) (j : Fin n), ext x (j.val + 1) = x j := by
              intro x j; unfold ShapeMoment.LogConcave.ext
              rw [dif_pos ⟨by omega, by omega⟩]; simp
            have hcoef0 : ∀ j : Fin n, ifrCoeff 0 j = if j.val = 0 then 1 else 0 := by
              intro j; unfold ifrCoeff; split_ifs <;> simp
            -- basic facts about feasible points
            have hbasic : ∀ y ∈ feasIFRPrime n m q, 1 ≤ n ∧ ext y 1 = 1 ∧ (∀ j, 0 ≤ ext y j) ∧
                (∀ i j, 1 ≤ i → i ≤ j → ext y j ≤ ext y i) ∧ (∀ j, ext y j ≤ 1) := by
              intro y hyS
              obtain ⟨hmom, hlc, hmono, hnn⟩ := hyS
              have hsum0 : ∑ j : Fin n, ifrCoeff 0 j * y j = 1 := by rw [hmom 0 (Nat.zero_le _), hq0]
              have hn : 1 ≤ n := by
                rcases Nat.eq_zero_or_pos n with h | h
                · subst h; simp at hsum0
                · exact h
              have h1 : ext y 1 = 1 := by
                have : ∑ j : Fin n, ifrCoeff 0 j * y j = y ⟨0, hn⟩ := by
                  rw [Finset.sum_eq_single ⟨0, hn⟩]
                  · rw [hcoef0]; simp
                  · intro j _ hj; rw [hcoef0, if_neg]; · simp
                    intro h; exact hj (Fin.ext h)
                  · simp
                unfold ShapeMoment.LogConcave.ext; rw [dif_pos ⟨le_rfl, hn⟩]; rw [← hsum0, this]
              have h0 : ∀ j, 0 ≤ ext y j := by
                intro j; unfold ShapeMoment.LogConcave.ext; split_ifs
                · exact hnn _
                · exact le_rfl
              have hanti : ∀ i j, 1 ≤ i → i ≤ j → ext y j ≤ ext y i := by
                intro i j hi hij
                induction j, hij using Nat.le_induction with
                | base => exact le_rfl
                | succ j hij ih =>
                  refine le_trans ?_ ih
                  by_cases hjn : j < n
                  · have := hmono j (by omega) hjn; linarith
                  · have : ext y (j+1) = 0 := by
                      unfold ShapeMoment.LogConcave.ext; rw [dif_neg]; omega
                    rw [this]; exact h0 j
              exact ⟨hn, h1, h0, hanti, fun j => by
                rcases Nat.eq_zero_or_pos j with h | h
                · subst h; unfold ShapeMoment.LogConcave.ext; rw [dif_neg (by omega)]; norm_num
                · rw [← h1]; exact hanti 1 j le_rfl h⟩
            constructor
            · have hsub : feasIFRPrime n m q ⊆ Set.Icc 0 1 := by
                intro y hy
                obtain ⟨_, _, h0, _, hle⟩ := hbasic y hy
                refine ⟨fun j => ?_, fun j => ?_⟩
                · have := h0 (j.val+1); rwa [hextval] at this
                · have := hle (j.val+1); rwa [hextval] at this
              have hcl : IsClosed (feasIFRPrime n m q) := by
                unfold feasIFRPrime
                simp only [Set.ofPred_and, Set.ofPred_forall]
                refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
                · refine isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
                  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
                · refine isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
                    isClosed_le ((hextc _).mul (hextc _)) ((hextc _).pow 2)
                · refine isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
                    isClosed_le continuous_const ((hextc _).sub (hextc _))
                · exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
              have hcpt : IsCompact (feasIFRPrime n m q) := isCompact_Icc.of_isClosed_subset hcl hsub
              have hobjc : Continuous (ifrObjective f) := by
                unfold ifrObjective
                exact continuous_finsetSum _ (fun j _ => continuous_const.mul ((hextc _).sub (hextc _)))
              have hobjlin : ∀ (y z : Fin n → ℝ) (a b : ℝ), ifrObjective f (a • y + b • z) =
                  a * ifrObjective f y + b * ifrObjective f z := by
                intro y z a b
                unfold ifrObjective
                simp only [hextlin]
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
              obtain ⟨x₀, hx₀S, hx₀⟩ := hcpt.exists_isMaxOn hfeas hobjc.continuousOn
              have hFc : IsCompact (feasIFRPrime n m q ∩ {y | ifrObjective f y = ifrObjective f x₀}) :=
                hcpt.inter_right (isClosed_eq hobjc continuous_const)
              obtain ⟨x, hx⟩ := hFc.extremePoints_nonempty ⟨x₀, hx₀S, rfl⟩
              have hxmax : ∀ z ∈ feasIFRPrime n m q, ifrObjective f z ≤ ifrObjective f x₀ :=
                fun z hz => isMaxOn_iff.mp hx₀ z hz
              rw [mem_extremePoints] at hx
              have hxv : ifrObjective f x = ifrObjective f x₀ := hx.1.2
              refine ⟨x, ?_, ⟨hx.1.1, fun z hz => hxv ▸ hxmax z hz⟩⟩
              rw [mem_extremePoints]
              refine ⟨hx.1.1, fun x₁ h₁ x₂ h₂ hseg => ?_⟩
              obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
              have e1 := hxmax x₁ h₁
              have e2 := hxmax x₂ h₂
              have hl := hobjlin x₁ x₂ a b
              rw [hxe, hxv] at hl
              have hsum : a * ifrObjective f x₀ + b * ifrObjective f x₀ = ifrObjective f x₀ := by
                rw [← add_mul, hab, one_mul]
              have k1 : ifrObjective f x₁ = ifrObjective f x₀ := by
                by_contra hne
                have hlt := lt_of_le_of_ne e1 hne
                linarith [mul_lt_mul_of_pos_left hlt ha, mul_le_mul_of_nonneg_left e2 hb.le]
              have k2 : ifrObjective f x₂ = ifrObjective f x₀ := by
                by_contra hne
                have hlt := lt_of_le_of_ne e2 hne
                linarith [mul_lt_mul_of_pos_left hlt hb, mul_le_mul_of_nonneg_left e1 ha.le]
              exact hx.2 x₁ ⟨h₁, k1⟩ x₂ ⟨h₂, k2⟩ ⟨a, b, ha, hb, hab, hxe⟩
            · intro y hy hmax
              have hyS : y ∈ feasIFRPrime n m q := hy.1
              obtain ⟨hn, h1, h0, hanti, hle1⟩ := hbasic y hyS
              obtain ⟨hmom, hlc, hmono, hnn⟩ := hyS
              have hextout : ∀ j, n < j → ext y j = 0 := by
                intro j hj; unfold ShapeMoment.LogConcave.ext; rw [dif_neg]; omega
              set k := Nat.findGreatest (fun j => 0 < ext y j) n with hkdef
              set a := Nat.findGreatest (fun j => ext y j = 1) n with hadef
              have hk_le : k ≤ n := Nat.findGreatest_le n
              have hk_pos : 0 < ext y k := Nat.findGreatest_spec (P := fun j => 0 < ext y j) hn (by rw [h1]; norm_num)
              have hk1 : 1 ≤ k := Nat.le_findGreatest (P := fun j => 0 < ext y j) hn (by rw [h1]; norm_num)
              have hk_gt : ∀ j, k < j → ext y j = 0 := by
                intro j hj
                by_cases hjn : j ≤ n
                · have := Nat.findGreatest_is_greatest (P := fun j => 0 < ext y j) hj hjn
                  simp only [not_lt] at this; exact le_antisymm this (h0 j)
                · exact hextout j (by omega)
              have hpos : ∀ j, 1 ≤ j → j ≤ k → 0 < ext y j := fun j hj1 hjk =>
                lt_of_lt_of_le hk_pos (hanti j k hj1 hjk)
              have ha_le : a ≤ n := Nat.findGreatest_le n
              have ha1v : ext y a = 1 := Nat.findGreatest_spec (P := fun j => ext y j = 1) hn h1
              have ha1 : 1 ≤ a := Nat.le_findGreatest (P := fun j => ext y j = 1) hn h1
              have hak : a ≤ k := Nat.le_findGreatest (P := fun j => 0 < ext y j) ha_le (by rw [ha1v]; norm_num)
              have hone : ∀ j, 1 ≤ j → j ≤ a → ext y j = 1 := fun j hj1 hja =>
                le_antisymm (hle1 j) (ha1v ▸ hanti j a hj1 hja)
              have hlt_a : ∀ j, a < j → ext y j < 1 := by
                intro j hj
                by_cases hjn : j ≤ n
                · have := Nat.findGreatest_is_greatest (P := fun j => ext y j = 1) hj hjn
                  exact lt_of_le_of_ne (hle1 j) this
                · rw [hextout j (by omega)]; norm_num
              have hstrict : ∀ j, a ≤ j → j < k → ext y (j + 1) < ext y j := by
                intro j hj
                induction j, hj using Nat.le_induction with
                | base => intro _; rw [ha1v]; exact hlt_a _ (by omega)
                | succ j hj ih =>
                  intro hjk
                  have ih' := ih (by omega)
                  have hp0 := hpos j (by omega) (by omega)
                  have hp1 := hpos (j+1) (by omega) (by omega)
                  have hl := hlc (j+1) (by omega) (by omega)
                  simp only [Nat.add_sub_cancel] at hl
                  by_contra hcon
                  push Not at hcon
                  nlinarith [mul_lt_mul_of_pos_left ih' hp1]
              set P : Finset ℕ := (Finset.range k).filter
                (fun p => a ≤ p ∧ (p = a ∨ ext y (p-1) * ext y (p+1) < ext y p ^ 2)) with hP
              have hPm : P.card ≤ m := by
                by_contra hcon
                push Not at hcon
                have hPmem : ∀ p ∈ P, p < k ∧ a ≤ p ∧ (p = a ∨ ext y (p-1) * ext y (p+1) < ext y p ^ 2) := by
                  intro p hp
                  simp only [hP, Finset.mem_filter, Finset.mem_range] at hp; exact ⟨hp.1, hp.2⟩
                let v : P → (Fin m → ℝ) := fun p i =>
                  ∑ j : Fin n, ifrCoeff (i.val + 1) j * (y j * ((j.val + 1 - p.val : ℕ) : ℝ))
                have hnli : ¬ LinearIndependent ℝ v := by
                  intro hli
                  have := hli.fintype_card_le_finrank
                  simp only [Fintype.card_coe, Module.finrank_fin_fun] at this
                  omega
                obtain ⟨g, hg, p₀, hp₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
                let δ : ℕ → ℝ := fun j => ∑ p : P, g p * ((j - p.val : ℕ) : ℝ)
                let d : Fin n → ℝ := fun j => y j * δ (j.val + 1)
                have hextd : ∀ (ε : ℝ) j, ext (y + ε • d) j = ext y j * (1 + ε * δ j) := by
                  intro ε j
                  unfold ShapeMoment.LogConcave.ext
                  split_ifs with h
                  · have : j - 1 + 1 = j := by omega
                    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, d, this]
                    ring
                  · simp
                have hδa : ∀ j, j ≤ a → δ j = 0 := by
                  intro j hj
                  apply Finset.sum_eq_zero
                  intro p _
                  have := (hPmem p.val p.2).2.1
                  rw [Nat.sub_eq_zero_of_le (le_trans hj this)]; simp
                have hdmom : ∀ i ≤ m, ∑ j, ifrCoeff i j * d j = 0 := by
                  intro i hi
                  rcases i with _ | i
                  · apply Finset.sum_eq_zero
                    intro j _
                    rw [hcoef0]
                    split_ifs with hj
                    · simp only [d, hj, zero_add, hδa 1 ha1]; ring
                    · ring
                  · have hg' := congrFun hg ⟨i, by omega⟩
                    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v,
                      Finset.mul_sum] at hg'
                    rw [Finset.sum_comm] at hg'
                    simp only [d, δ, Finset.mul_sum]
                    rw [← hg']
                    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
                    ring
                have hd0 : d ≠ 0 := by
                  have hS : (Finset.univ.filter (fun p : P => g p ≠ 0)).Nonempty := ⟨p₀, by simp [hp₀]⟩
                  set p₁ := (Finset.univ.filter (fun p : P => g p ≠ 0)).min' hS with hp₁
                  have hp₁mem := Finset.min'_mem _ hS
                  rw [← hp₁] at hp₁mem
                  have hg₁ : g p₁ ≠ 0 := by simpa using hp₁mem
                  have hmin : ∀ p : P, g p ≠ 0 → p₁ ≤ p := fun p hp =>
                    Finset.min'_le _ _ (by simp [hp])
                  have hδ₁ : δ (p₁.val + 1) = g p₁ := by
                    simp only [δ]
                    rw [Finset.sum_eq_single p₁]
                    · simp
                    · intro p _ hne
                      by_cases hgp : g p = 0
                      · simp [hgp]
                      · have h1' := hmin p hgp
                        have h2' : p₁.val < p.val := lt_of_le_of_ne h1' (fun h => hne (Subtype.ext h).symm)
                        rw [Nat.sub_eq_zero_of_le (by omega)]; simp
                    · simp
                  have hp₁k := (hPmem p₁.val p₁.2).1
                  intro hd
                  have := congrFun hd ⟨p₁.val, by omega⟩
                  simp only [d, Pi.zero_apply, hδ₁] at this
                  have hy₁ : 0 < y ⟨p₁.val, by omega⟩ := by
                    rw [← hextval y ⟨p₁.val, by omega⟩]; exact hpos _ (by simp) (by simp; omega)
                  rcases mul_eq_zero.mp this with h | h
                  · exact hy₁.ne' h
                  · exact hg₁ h
                -- local feasibility
                let E : ℕ → ℝ → ℝ := fun j ε => ext y j * (1 + ε * δ j)
                have hcont : ∀ j, Continuous (E j) := fun j => by fun_prop
                have hevlt : ∀ (F G : ℝ → ℝ), Continuous F → Continuous G → F 0 < G 0 →
                    ∀ᶠ ε in nhds (0:ℝ), F ε < G ε := fun F G hF hG h =>
                  ContinuousAt.eventually_lt hF.continuousAt hG.continuousAt h
                have hE0 : ∀ j, E j 0 = ext y j := fun j => by simp [E]
                have hC1 : ∀ j, ∀ᶠ ε in nhds (0:ℝ), 0 ≤ E j ε := by
                  intro j
                  by_cases h : ext y j = 0
                  · exact Filter.Eventually.of_forall fun ε => by simp [E, h]
                  · have hp : 0 < ext y j := lt_of_le_of_ne (h0 j) (Ne.symm h)
                    have := hevlt (fun _ => 0) (E j) continuous_const (hcont j) (by rw [hE0]; exact hp)
                    filter_upwards [this] with ε hε using hε.le
                have hC2 : ∀ j, ∀ᶠ ε in nhds (0:ℝ), 1 ≤ j → j < n → 0 ≤ E j ε - E (j+1) ε := by
                  intro j
                  by_cases hja : j < a
                  · refine Filter.Eventually.of_forall fun ε h1j _ => ?_
                    simp only [E, hδa j (by omega), hδa (j+1) (by omega), hone j h1j (by omega),
                      hone (j+1) (by omega) (by omega)]
                    simp
                  · by_cases hjk : j < k
                    · have := hevlt (E (j+1)) (E j) (hcont _) (hcont _)
                        (by rw [hE0, hE0]; exact hstrict j (by omega) hjk)
                      filter_upwards [this] with ε hε using fun _ _ => by linarith
                    · filter_upwards [hC1 j] with ε hε
                      intro _ _
                      have : E (j+1) ε = 0 := by simp [E, hk_gt (j+1) (by omega)]
                      rw [this]; linarith
                have hC3 : ∀ j, ∀ᶠ ε in nhds (0:ℝ), 1 < j → j < n →
                    E (j-1) ε * E (j+1) ε ≤ E j ε ^ 2 := by
                  intro j
                  by_cases hj : 1 < j ∧ j < n
                  · have hlcj := hlc j hj.1 hj.2
                    by_cases hz : ext y j = 0
                    · refine Filter.Eventually.of_forall fun ε _ _ => ?_
                      have : ext y (j+1) = 0 := le_antisymm (hz ▸ hanti j (j+1) (by omega) (by omega)) (h0 _)
                      have : E (j+1) ε = 0 := by simp [E, this]
                      rw [this, mul_zero]; positivity
                    · by_cases hs : ext y (j-1) * ext y (j+1) < ext y j ^ 2
                      · have := hevlt (fun ε => E (j-1) ε * E (j+1) ε) (fun ε => E j ε ^ 2)
                          ((hcont _).mul (hcont _)) ((hcont _).pow 2) (by simp only [hE0]; exact hs)
                        filter_upwards [this] with ε hε using fun _ _ => hε.le
                      · have heq : ext y (j-1) * ext y (j+1) = ext y j ^ 2 := le_antisymm hlcj (not_lt.mp hs)
                        have hjP : j ∉ P := by
                          intro hjP
                          obtain ⟨_, _, hor⟩ := hPmem j hjP
                          rcases hor with hja | hs'
                          · subst hja
                            rw [hone (a-1) (by omega) (by omega), ha1v] at heq
                            have := hlt_a (a+1) (by omega)
                            linarith
                          · exact hs hs'
                        have hlin : δ (j-1) + δ (j+1) = 2 * δ j := by
                          simp only [δ, ← Finset.sum_add_distrib, Finset.mul_sum]
                          refine Finset.sum_congr rfl fun p _ => ?_
                          have hpj : p.val ≠ j := fun h => hjP (h ▸ p.2)
                          have hnat : (j - 1 - p.val) + (j + 1 - p.val) = 2 * (j - p.val) := by omega
                          have hc : ((j - 1 - p.val : ℕ) : ℝ) + ((j + 1 - p.val : ℕ) : ℝ) =
                              2 * ((j - p.val : ℕ) : ℝ) := by exact_mod_cast hnat
                          rw [← mul_add, hc]; ring
                        refine Filter.Eventually.of_forall fun ε _ _ => ?_
                        have hB' : δ (j+1) = 2 * δ j - δ (j-1) := by linarith
                        have : E (j-1) ε * E (j+1) ε =
                            (ext y (j-1) * ext y (j+1)) * ((1 + ε * δ (j-1)) * (1 + ε * δ (j+1))) := by
                          simp only [E]; ring
                        rw [this, heq, hB']
                        simp only [E]
                        nlinarith [sq_nonneg (ext y j * ε * (δ (j-1) - δ j))]
                  · exact Filter.Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hj
                have hev : ∀ᶠ ε in nhds (0:ℝ), y + ε • d ∈ feasIFRPrime n m q := by
                  have hall := (Filter.eventually_all_finset (Finset.range (n+1))).mpr
                    (fun j _ => (hC1 j).and ((hC2 j).and (hC3 j)))
                  filter_upwards [hall] with ε hε
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · intro i hi
                    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
                    rw [hmom i hi]
                    have : ∑ j, ifrCoeff i j * (ε * d j) = ε * ∑ j, ifrCoeff i j * d j := by
                      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
                    rw [this, hdmom i hi]; ring
                  · intro j h1j h2j
                    rw [hextd, hextd, hextd]
                    exact (hε j (by simp; omega)).2.2 h1j h2j
                  · intro j h1j h2j
                    rw [hextd, hextd]
                    exact (hε j (by simp; omega)).2.1 h1j h2j
                  · intro j
                    rw [← hextval (y + ε • d) j, hextd]
                    exact (hε (j.val+1) (by simp)).1
                obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
                have hA := hball (y := η/2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
                have hB := hball (y := -(η/2)) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
                have hseg : y ∈ openSegment ℝ (y + (η/2) • d) (y + (-(η/2)) • d) :=
                  ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
                    funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
                have := ((mem_extremePoints.mp hy).2 _ hA _ hB hseg).1
                apply hd0
                have h2 : (η/2) • d = 0 := by
                  have := congrArg (fun z => z - y) this
                  simpa using this
                rcases smul_eq_zero.mp h2 with h | h
                · linarith
                · exact h
              have hkP : k ∉ P := by simp [hP]
              have hQcard : (insert k P).card = P.card + 1 := Finset.card_insert_of_notMem hkP
              have hQmem : ∀ x ∈ insert k P, a ≤ x ∧ x ≤ k := by
                intro x hx
                rcases Finset.mem_insert.mp hx with h | h
                · omega
                · simp only [hP, Finset.mem_filter, Finset.mem_range] at h; omega
              have haQ : a ∈ insert k P := by
                rcases eq_or_lt_of_le hak with h | h
                · rw [h]; exact Finset.mem_insert_self _ _
                · apply Finset.mem_insert_of_mem
                  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, le_rfl, Or.inl rfl⟩
              have hkQ : k ∈ insert k P := Finset.mem_insert_self _ _
              set b := (insert k P).orderEmbOfFin hQcard with hb
              have hbmem : ∀ i, b i ∈ insert k P := fun i => Finset.orderEmbOfFin_mem _ _ i
              have hbrange : ∀ x ∈ insert k P, ∃ l, b l = x := by
                intro x hx
                have : x ∈ Set.range b := by rw [hb, Finset.range_orderEmbOfFin]; exact hx
                exact this
              have hbetween : ∀ i : Fin P.card, ∀ x, b i.castSucc < x → x < b i.succ →
                  ext y (x-1) * ext y (x+1) = ext y x ^ 2 := by
                intro i x h1x h2x
                have hxQ : x ∉ insert k P := by
                  intro hx
                  obtain ⟨l, rfl⟩ := hbrange x hx
                  have e1 := b.lt_iff_lt.mp h1x
                  have e2 := b.lt_iff_lt.mp h2x
                  rw [Fin.lt_def] at e1 e2
                  simp at e1 e2
                  omega
                have hB := hQmem _ (hbmem i.castSucc)
                have hE := hQmem _ (hbmem i.succ)
                have hxP : x ∉ P := fun h => hxQ (Finset.mem_insert_of_mem h)
                simp only [hP, Finset.mem_filter, Finset.mem_range, not_and, not_or, not_lt] at hxP
                have hns := (hxP (by omega) (by omega)).2
                exact le_antisymm (hlc x (by omega) (by omega)) hns
              refine ⟨a, k, P.card, fun i => b i, fun i => ext y (b i.castSucc),
                fun i => ext y (b i.castSucc + 1) / ext y (b i.castSucc), ha1, hak, hk_le, hPm, hone,
                hstrict, hpos, hk_gt, b.strictMono, ?_, ?_, ?_, ?_⟩
              · obtain ⟨l, hl⟩ := hbrange a haQ
                apply le_antisymm
                · rw [← hl]; exact b.monotone (Fin.zero_le _)
                · exact (hQmem _ (hbmem 0)).1
              · obtain ⟨l, hl⟩ := hbrange k hkQ
                apply le_antisymm
                · exact (hQmem _ (hbmem _)).2
                · rw [← hl]; exact b.monotone (Fin.le_last _)
              · intro i
                have hB := hQmem _ (hbmem i.castSucc)
                have hE := hQmem _ (hbmem i.succ)
                have hBE : b i.castSucc < b i.succ := b.strictMono Fin.castSucc_lt_succ
                have hα := hpos (b i.castSucc) (by omega) (by omega)
                refine ⟨hα, div_pos (hpos _ (by omega) (by omega)) hα, ?_⟩
                rw [div_lt_one hα]
                exact hstrict _ (by omega) (by omega)
              · intro i j hj1 hj2
                have hB := hQmem _ (hbmem i.castSucc)
                have hE := hQmem _ (hbmem i.succ)
                have hBE : b i.castSucc < b i.succ := b.strictMono Fin.castSucc_lt_succ
                have hα := hpos (b i.castSucc) (by omega) (by omega)
                have hbt := hbetween i
                simp only at hj1 hj2 ⊢
                generalize b i.castSucc = B at *
                generalize b i.succ = E at *
                have hgeo : ∀ t, B + t ≤ E → ext y (B + t) = ext y B * (ext y (B+1) / ext y B) ^ t := by
                  intro t
                  induction t using Nat.strong_induction_on with
                  | _ t ih =>
                    intro ht
                    rcases t with _ | _ | t
                    · simp
                    · simp only [zero_add, pow_one]; field_simp
                    · have e1 := ih t (by omega) (by omega)
                      have e2 := ih (t+1) (by omega) (by omega)
                      have hbx := hbt (B + t + 1) (by omega) (by omega)
                      have h3 : B + t + 1 - 1 = B + t := by omega
                      rw [h3] at hbx
                      rw [show B + (t + 1) = B + t + 1 by omega] at e2
                      rw [show B + (t + 1 + 1) = B + t + 1 + 1 by omega]
                      have hp : ext y B * (ext y (B+1) / ext y B) ^ t ≠ 0 := by
                        rw [← e1]; exact (hpos _ (by omega) (by omega)).ne'
                      apply mul_left_cancel₀ hp
                      calc ext y B * (ext y (B+1) / ext y B) ^ t * ext y (B + t + 1 + 1)
                          = ext y (B + t) * ext y (B + t + 1 + 1) := by rw [e1]
                        _ = ext y (B + t + 1) ^ 2 := hbx
                        _ = (ext y B * (ext y (B+1) / ext y B) ^ (t + 1)) ^ 2 := by rw [e2]
                        _ = _ := by ring
                have := hgeo (j - B) (by omega)
                rw [show B + (j - B) = j by omega] at this
                exact this
