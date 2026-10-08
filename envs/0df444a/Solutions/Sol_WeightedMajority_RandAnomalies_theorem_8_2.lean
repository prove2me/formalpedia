-- Prove2me | solution 1 for WeightedMajority.RandAnomalies.theorem_8_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:33:08.540877+00:00
-- url     : https://prove2.me/submissions/105107e2-461c-409d-ae6b-6636fdb277ee

import Definitions.Def_WeightedMajority_RandAnomalies_OptRand

open scoped ENNReal


namespace WeightedMajority.RandAnomalies

open UnderstandingML

variable {X : Type*}

noncomputable def lossAux (A : OnlineAlgR X) : List (X × Bool) → List (X × Bool) → ℝ
  | _, [] => 0
  | h, e :: r => |A h e.1 - labelR e.2| + lossAux A (h ++ [e]) r

lemma lossAux_append (A : OnlineAlgR X) (m m' h : List (X × Bool)) :
    lossAux A h (m ++ m') = lossAux A h m + lossAux A (h ++ m) m' := by
  induction m generalizing h with
  | nil => simp [lossAux]
  | cons e r ih => simp [lossAux, ih, add_assoc]

lemma lossAux_nonneg (A : OnlineAlgR X) (m h : List (X × Bool)) : 0 ≤ lossAux A h m := by
  induction m generalizing h with
  | nil => simp [lossAux]
  | cons e r ih => simp only [lossAux]; exact add_nonneg (abs_nonneg _) (ih _)

lemma sumAux (A : OnlineAlgR X) (l h : List (X × Bool)) :
    ∑ i : Fin l.length, |A (h ++ l.take i) (l.get i).1 - labelR (l.get i).2| = lossAux A h l := by
  induction l generalizing h with
  | nil => simp [lossAux]
  | cons e r ih =>
    refine (Fin.sum_univ_succ _).trans ?_
    simp only [lossAux, ← ih]
    simp [List.append_assoc]

lemma cumLoss_get (A : OnlineAlgR X) (l : List (X × Bool)) :
    cumLoss A (fun i : Fin l.length => l.get i) = lossAux A [] l := by
  rw [← sumAux A l []]
  simp [cumLoss, history, List.ofFn_get]

lemma anomalies_get (f : X → Bool) (l : List (X × Bool)) :
    WeightedMajority.Anomalies.anomalies f (fun i : Fin l.length => l.get i)
      = l.countP (fun e => decide (f e.1 ≠ e.2)) := by
  induction l with
  | nil => simp [WeightedMajority.Anomalies.anomalies]
  | cons e r ih =>
    unfold WeightedMajority.Anomalies.anomalies at *
    refine (Fin.card_filter_univ_succ (n := r.length)
      (fun t : Fin (r.length+1) => f ((e::r).get t).1 ≠ ((e::r).get t).2)).trans ?_
    simp only [List.countP_cons]
    simp only [List.get_eq_getElem, Fin.val_succ, Fin.val_zero, List.getElem_cons_succ,
      List.getElem_cons_zero] at ih ⊢
    rw [ih]
    split_ifs <;> simp_all

lemma mistakes_le (A : OnlineAlgR X) (hA : IsRandAlg A) {T : ℕ} (S : Fin T → X × Bool) :
    (mistakes (fun hist x => decide (1/2 ≤ A hist x)) S : ℝ) ≤ 2 * cumLoss A S := by
  classical
  have h1 := Finset.card_nsmul_le_sum
    (Finset.univ.filter (fun t : Fin T ↦ decide (1/2 ≤ A (history S t) (S t).1) ≠ (S t).2))
    (fun t => |A (history S t) (S t).1 - labelR (S t).2|) (1/2 : ℝ) (by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hp := hA (history S t) (S t).1
      obtain ⟨hp0, hp1⟩ := hp
      generalize A (history S t) (S t).1 = p at *
      generalize (S t).2 = y at *
      cases y
      · have hh : 1/2 ≤ p := by simpa using ht
        simp only [labelR, Bool.false_eq_true, if_false, sub_zero]
        rw [abs_of_nonneg hp0]; exact hh
      · have hh : ¬ 1/2 ≤ p := by simpa using ht
        simp only [labelR, if_true]
        rw [abs_of_nonpos (by linarith)]; linarith)
  have h2 : ∑ t ∈ Finset.univ.filter (fun t : Fin T ↦ decide (1/2 ≤ A (history S t) (S t).1) ≠ (S t).2),
      |A (history S t) (S t).1 - labelR (S t).2| ≤ cumLoss A S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
  unfold mistakes
  simp only [nsmul_eq_mul] at h1
  linarith

lemma ext_exists (A : OnlineAlgR X) (hA : IsRandAlg A) (x0 : X) (a : Bool) (k : ℕ) :
    ∀ (h : List (X × Bool)) (ε : ℝ), 0 < ε → ∃ ext : List (X × Bool),
      (∀ e ∈ ext, e.1 = x0) ∧ ext.countP (fun e => decide (e.2 ≠ a)) ≤ k ∧
      (k : ℝ) - ε ≤ lossAux A h ext := by
  induction k with
  | zero =>
    intro h ε hε
    exact ⟨[], by simp, by simp, by simp [lossAux]; linarith⟩
  | succ k ih =>
    intro h ε hε
    set u : ℕ → ℝ := fun n => |A (h ++ List.replicate n (x0, a)) x0 - labelR a| with hu
    by_cases hex : ∃ n, u n ≤ ε / 2
    · obtain ⟨n, hn⟩ := hex
      obtain ⟨ext', hext1, hext2, hext3⟩ :=
        ih (h ++ List.replicate n (x0, a) ++ [(x0, !a)]) (ε / 2) (by linarith)
      refine ⟨List.replicate n (x0, a) ++ ((x0, !a) :: ext'), ?_, ?_, ?_⟩
      · intro e he
        simp only [List.mem_append, List.mem_replicate, List.mem_cons] at he
        rcases he with ⟨_, rfl⟩ | rfl | he
        · rfl
        · rfl
        · exact hext1 e he
      · rw [List.countP_append, List.countP_cons]
        simp [List.countP_replicate]
        cases a <;> simp at hext2 ⊢ <;> omega
      · rw [lossAux_append]
        simp only [lossAux]
        have h0 := lossAux_nonneg A (List.replicate n (x0, a)) h
        have hb : |A (h ++ List.replicate n (x0, a)) x0 - labelR (!a)| = 1 - u n := by
          have hp := hA (h ++ List.replicate n (x0, a)) x0
          obtain ⟨hp0, hp1⟩ := hp
          simp only [hu]
          generalize A (h ++ List.replicate n (x0, a)) x0 = p at *
          cases a <;> simp [labelR] <;>
            rw [abs_of_nonneg hp0, abs_of_nonpos (show p - 1 ≤ 0 by linarith)] <;> ring
        rw [hb]
        push_cast
        have : h ++ List.replicate n (x0, a) ++ [(x0, !a)] = h ++ List.replicate n (x0, a) ++ [(x0, !a)] := rfl
        linarith
    · push_neg at hex
      have key : ∀ n : ℕ, (n : ℝ) * (ε / 2) ≤ lossAux A h (List.replicate n (x0, a)) := by
        intro n
        induction n with
        | zero => simp [lossAux]
        | succ n ihn =>
          rw [List.replicate_succ', lossAux_append]
          simp only [lossAux, add_zero]
          have := hex n
          push_cast
          nlinarith
      obtain ⟨n, hn⟩ := exists_nat_gt (((k : ℝ) + 1) / (ε / 2))
      refine ⟨List.replicate n (x0, a), ?_, ?_, ?_⟩
      · intro e he; simp [List.mem_replicate] at he; rw [he.2]
      · simp [List.countP_replicate]
      · have := key n
        rw [div_lt_iff₀ (by linarith)] at hn
        push_cast
        nlinarith

lemma cumLoss_ofFn (A : OnlineAlgR X) {T : ℕ} (S : Fin T → X × Bool) :
    cumLoss A S = lossAux A [] (List.ofFn S) := by
  rw [← cumLoss_get A (List.ofFn S)]
  unfold cumLoss
  refine Finset.sum_equiv (finCongr (by simp)) (by simp) (fun i _ => ?_)
  simp [history, List.get_ofFn]

lemma anomalies_ofFn (f : X → Bool) {T : ℕ} (S : Fin T → X × Bool) :
    WeightedMajority.Anomalies.anomalies f S
      = (List.ofFn S).countP (fun e => decide (f e.1 ≠ e.2)) := by
  rw [← anomalies_get]
  unfold WeightedMajority.Anomalies.anomalies
  refine Finset.card_equiv (finCongr (by simp)) (fun i => ?_)
  simp [List.get_ofFn]

lemma key (A : OnlineAlgR X) (hA : IsRandAlg A) (F : Set (X → Bool)) (x0 : X) (η : ℕ)
    {T : ℕ} (S0 : Fin T → X × Bool) (h0 : InSEta F 0 S0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T' : ℕ) (S' : Fin T' → X × Bool), InSEta F η S' ∧ cumLoss A S0 + η - ε ≤ cumLoss A S' := by
  obtain ⟨f1, hf1, hanom⟩ := h0
  obtain ⟨ext, he1, he2, he3⟩ := ext_exists A hA x0 (f1 x0) η (List.ofFn S0) ε hε
  refine ⟨(List.ofFn S0 ++ ext).length, fun i => (List.ofFn S0 ++ ext).get i, ⟨f1, hf1, ?_⟩, ?_⟩
  · rw [anomalies_get, List.countP_append]
    have hS : (List.ofFn S0).countP (fun e => decide (f1 e.1 ≠ e.2)) = 0 := by
      have := anomalies_ofFn f1 S0
      omega
    have hE : ext.countP (fun e => decide (f1 e.1 ≠ e.2)) ≤ η := by
      refine le_trans (le_of_eq ?_) he2
      apply List.countP_congr
      intro e he
      rw [he1 e he]
      simp only [decide_eq_true_eq]; exact ne_comm
    omega
  · rw [cumLoss_get, lossAux_append, cumLoss_ofFn A S0]
    simp only [List.nil_append]
    linarith


lemma main_bound {F : Set (X → Bool)} (hF : F.Nontrivial) (η : ℕ) (A : OnlineAlgR X) (hA : IsRandAlg A)
    (N : ℕ) (hN : (N : ℕ∞) ≤ WeightedMajority.Anomalies.opt F 0) :
    (N : ℝ≥0∞) / 2 + η ≤
      ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : InSEta F η S), ENNReal.ofReal (cumLoss A S) := by
  classical
  obtain ⟨f, hf, g, hg, hfg⟩ := hF
  obtain ⟨x0, hx0⟩ : ∃ x, f x ≠ g x := by
    by_contra hc; push_neg at hc; exact hfg (funext hc)
  -- there is a realizable S0 with at least N mistakes of the rounded algorithm
  set B : OnlineAlg X Bool := fun hist x => decide (1/2 ≤ A hist x) with hB
  have hreal : ∃ (T : ℕ) (S0 : Fin T → X × Bool), InSEta F 0 S0 ∧ N ≤ mistakes B S0 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      refine ⟨0, fun i => i.elim0, ⟨f, hf, ?_⟩, Nat.zero_le _⟩
      simp [WeightedMajority.Anomalies.anomalies]
    · by_contra hc
      push_neg at hc
      have : WeightedMajority.Anomalies.opt F 0 ≤ ((N - 1 : ℕ) : ℕ∞) := by
        refine (iInf_le _ B).trans ?_
        refine iSup_le fun T => iSup_le fun S => iSup_le fun hS => ?_
        have := hc T S hS
        exact_mod_cast (by omega : mistakes B S ≤ N - 1)
      have h2 : ((N : ℕ) : ℕ∞) ≤ ((N - 1 : ℕ) : ℕ∞) := hN.trans this
      have h3 : N ≤ N - 1 := by exact_mod_cast h2
      omega
  obtain ⟨T, S0, hS0, hm⟩ := hreal
  have hmis := mistakes_le A hA S0
  have hmN : (N : ℝ) ≤ 2 * cumLoss A S0 := le_trans (by exact_mod_cast hm) hmis
  have hcl : (N : ℝ) / 2 + η ≤ cumLoss A S0 + η := by linarith
  -- now approximate
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  obtain ⟨T', S', hS', hle⟩ := key A hA F x0 η S0 hS0 (ε : ℝ) (by exact_mod_cast hε)
  have h1 : ENNReal.ofReal (cumLoss A S') ≤
      ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : InSEta F η S), ENNReal.ofReal (cumLoss A S) :=
    le_iSup_of_le T' (le_iSup_of_le S' (le_iSup_of_le hS' le_rfl))
  have h2 : (N : ℝ≥0∞) / 2 + η ≤ ENNReal.ofReal (cumLoss A S') + ε := by
    have : (N : ℝ≥0∞) / 2 + η = ENNReal.ofReal ((N : ℝ) / 2 + η) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp [ENNReal.ofReal_div_of_pos]
    rw [this]
    calc ENNReal.ofReal ((N : ℝ) / 2 + η) ≤ ENNReal.ofReal (cumLoss A S' + ε) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (cumLoss A S') + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = _ := by simp
  exact h2.trans (add_le_add_left h1 _)

theorem wm_core {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    ((WeightedMajority.Anomalies.opt F 0 : ℕ∞) : ℝ≥0∞) / 2 + η ≤ optRand F η := by
  unfold optRand
  refine le_iInf₂ (fun A hA => ?_)
  generalize hd : WeightedMajority.Anomalies.opt F 0 = d
  induction d using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top]
    have : ∀ N : ℕ, (N : ℝ≥0∞) / 2 ≤
        ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : InSEta F η S), ENNReal.ofReal (cumLoss A S) := by
      intro N
      exact le_trans le_self_add (main_bound hF η A hA N (by rw [hd]; exact le_top))
    rw [show ((⊤ : ℝ≥0∞) / 2 + η) = ⊤ by rw [ENNReal.top_div_of_ne_top (by norm_num)]; simp]
    by_contra hc
    rw [not_le] at hc
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hc.ne
    have h2 := this (2 * n)
    have h3 : ((2 * n : ℕ) : ℝ≥0∞) / 2 = n := by
      push_cast
      rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    rw [h3] at h2
    exact absurd hn (not_lt.mpr h2)
  | coe n =>
    simp only [ENat.toENNReal_coe]
    exact main_bound hF η A hA n (by rw [hd])

end WeightedMajority.RandAnomalies

open WeightedMajority.RandAnomalies


theorem solution {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    ((WeightedMajority.Anomalies.opt F 0 : ℕ∞) : ℝ≥0∞) / 2 + η ≤ optRand F η := by
  exact wm_core F hF η
