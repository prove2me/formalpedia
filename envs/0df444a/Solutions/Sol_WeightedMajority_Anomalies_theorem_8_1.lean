-- Prove2me | solution 1 for WeightedMajority.Anomalies.theorem_8_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:50:02.438021+00:00
-- url     : https://prove2.me/submissions/70d9b029-8dd2-460b-b86f-b735987f3de5

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_WeightedMajority_Anomalies_Opt



namespace WeightedMajority.Anomalies

open UnderstandingML

section Aux
variable {X : Type*}

def Shat (H : Set (X → Bool)) (d : ℕ) : Prop := ∃ v : List Bool → X, ShattersTree H d v

lemma shatters_succ_iff (H : Set (X → Bool)) (d : ℕ) (v : List Bool → X) :
    ShattersTree H (d+1) v ↔
      (ShattersTree {h ∈ H | h (v []) = true} d (fun l => v (true :: l)) ∧
      ShattersTree {h ∈ H | h (v []) = false} d (fun l => v (false :: l))) := by
  have fwd : ∀ b : Bool, ShattersTree H (d+1) v →
      ShattersTree {h ∈ H | h (v []) = b} d (fun l => v (b :: l)) := by
    intro b hv y'
    obtain ⟨h, hH, hy⟩ := hv (Fin.cons b y')
    refine ⟨h, ⟨hH, ?_⟩, fun s => ?_⟩
    · have := hy 0
      simpa using this
    · have := hy s.succ
      simp only [List.ofFn_succ, Fin.cons_succ] at this
      convert this using 4
      · simp
      · congr 1
  constructor
  · intro hv
    exact ⟨fwd true hv, fwd false hv⟩
  · rintro ⟨ht, hf⟩ y
    have bwd : ∀ b : Bool, ShattersTree {h ∈ H | h (v []) = b} d (fun l => v (b :: l)) →
        y 0 = b → ∃ h ∈ H, ∀ t : Fin (d+1),
          h (v (List.ofFn (fun j : Fin (t : ℕ) ↦ y ⟨j, lt_trans j.2 t.2⟩))) = y t := by
      intro b hb hyb
      obtain ⟨h, ⟨hH, hh0⟩, hy⟩ := hb (fun i => y i.succ)
      refine ⟨h, hH, fun t => ?_⟩
      refine Fin.cases ?_ (fun s => ?_) t
      · simpa [hyb] using hh0
      · have := hy s
        simpa [List.ofFn_succ, hyb] using this
    cases hy0 : y 0
    · exact bwd false hf hy0
    · exact bwd true ht hy0

lemma shat_zero_iff (H : Set (X → Bool)) (x₀ : X) : Shat H 0 ↔ H.Nonempty := by
  constructor
  · rintro ⟨v, h⟩
    obtain ⟨f, hf, _⟩ := h (fun i => i.elim0)
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨fun _ => x₀, fun y => ⟨f, hf, fun t => t.elim0⟩⟩

lemma shat_zero_nonempty (H : Set (X → Bool)) (h : Shat H 0) : H.Nonempty := by
  obtain ⟨v, h⟩ := h
  obtain ⟨f, hf, _⟩ := h (fun i => i.elim0)
  exact ⟨f, hf⟩

lemma shat_succ_iff (H : Set (X → Bool)) (d : ℕ) :
    Shat H (d+1) ↔ ∃ x : X, Shat {h ∈ H | h x = true} d ∧ Shat {h ∈ H | h x = false} d := by
  constructor
  · rintro ⟨v, hv⟩
    rw [shatters_succ_iff] at hv
    exact ⟨v [], ⟨_, hv.1⟩, ⟨_, hv.2⟩⟩
  · rintro ⟨x, ⟨vt, ht⟩, ⟨vf, hf⟩⟩
    let w : List Bool → X := fun l => match l with
      | [] => x
      | true :: l => vt l
      | false :: l => vf l
    exact ⟨w, (shatters_succ_iff H d w).2 ⟨ht, hf⟩⟩

lemma shat_mono {H H' : Set (X → Bool)} (hsub : H ⊆ H') {d : ℕ} (h : Shat H d) : Shat H' d := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, fun y => by
    obtain ⟨f, hf, e⟩ := hv y
    exact ⟨f, hsub hf, e⟩⟩

lemma shat_pred (d : ℕ) : ∀ (H : Set (X → Bool)), Shat H (d+1) → Shat H d := by
  induction d with
  | zero =>
    intro H h
    obtain ⟨x, ht, _⟩ := (shat_succ_iff H 0).1 h
    exact (shat_zero_iff H x).2 (by
      obtain ⟨f, hf, _⟩ := shat_zero_nonempty _ ht
      exact ⟨f, hf⟩)
  | succ d ih =>
    intro H h
    obtain ⟨x, ht, hf⟩ := (shat_succ_iff H (d+1)).1 h
    exact (shat_succ_iff H d).2 ⟨x, ih _ ht, ih _ hf⟩

lemma shat_le {H : Set (X → Bool)} {d e : ℕ} (h : Shat H d) (he : e ≤ d) : Shat H e := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  clear he
  induction k with
  | zero => exact h
  | succ k ih => exact ih (shat_pred _ _ h)

lemma ldim_mono {H H' : Set (X → Bool)} (hsub : H ⊆ H') : ldim H ≤ ldim H' := by
  unfold ldim
  refine iSup₂_le fun d hd => ?_
  exact le_iSup₂_of_le d (shat_mono hsub hd) le_rfl

lemma le_ldim {H : Set (X → Bool)} {d : ℕ} (h : Shat H d) : (d : ℕ∞) ≤ ldim H := by
  unfold ldim
  exact le_iSup₂_of_le d h le_rfl

lemma ex_shat_of_le {H : Set (X → Bool)} (x₀ : X) (hne : H.Nonempty) (k : ℕ)
    (hk : (k : ℕ∞) ≤ ldim H) : Shat H k := by
  by_contra hn
  have h0 : Shat H 0 := (shat_zero_iff H x₀).2 hne
  have hlt : ∀ d, Shat H d → d < k := by
    intro d hd
    by_contra hdk
    exact hn (shat_le hd (by omega))
  have hkpos : 0 < k := hlt 0 h0
  have : ldim H ≤ ((k - 1 : ℕ) : ℕ∞) := by
    unfold ldim
    refine iSup₂_le fun d hd => ?_
    have := hlt d hd
    exact_mod_cast (by omega : d ≤ k - 1)
  have h2 : ((k : ℕ) : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := hk.trans this
  have h3 : k ≤ k - 1 := by exact_mod_cast h2
  omega

section Mist
variable {Y : Type*} [DecidableEq Y]

lemma history_cons_zero {n : ℕ} (s : X × Y) (S : Fin n → X × Y) :
    history (Fin.cons s S : Fin (n+1) → X × Y) 0 = [] := by
  simp [history]

lemma history_cons_succ {n : ℕ} (s : X × Y) (S : Fin n → X × Y) (t : Fin n) :
    history (Fin.cons s S : Fin (n+1) → X × Y) ((t.succ : Fin (n+1)) : ℕ) = s :: history S t := by
  simp [history, List.ofFn_succ, Fin.cons_succ]

lemma mistakes_cons (A : OnlineAlg X Y) {n : ℕ} (s : X × Y) (S : Fin n → X × Y) :
    mistakes A (Fin.cons s S : Fin (n+1) → X × Y) =
      (if A [] s.1 ≠ s.2 then 1 else 0) + mistakes (fun h y => A (s :: h) y) S := by
  unfold mistakes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, history_cons_zero, history_cons_succ]

end Mist

lemma anomalies_cons (f : X → Bool) {n : ℕ} (s : X × Bool) (S : Fin n → X × Bool) :
    anomalies f (Fin.cons s S : Fin (n+1) → X × Bool) =
      (if f s.1 ≠ s.2 then 1 else 0) + anomalies f S := by
  unfold anomalies
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma error_path (x : X) : ∀ (n : ℕ) (A : OnlineAlg X Bool),
    ∃ S : Fin n → X × Bool, (∀ t, (S t).1 = x) ∧ mistakes A S = n := by
  intro n
  induction n with
  | zero =>
    intro A
    exact ⟨fun t => t.elim0, fun t => t.elim0, by simp [mistakes]⟩
  | succ n ih =>
    intro A
    obtain ⟨S', h1, h2⟩ := ih (fun h y => A ((x, !A [] x) :: h) y)
    refine ⟨Fin.cons (x, !A [] x) S', fun t => ?_, ?_⟩
    · refine Fin.cases ?_ (fun s => ?_) t
      · simp
      · simpa using h1 s
    · have key : (if A [] (x, !A [] x).1 ≠ (x, !A [] x).2 then 1 else 0 : ℕ) = 1 := by
        cases h : A [] x <;> simp [h]
      rw [mistakes_cons, h2, key]; omega

lemma base_case {F : Set (X → Bool)} (hF : Shat F 1) (A : OnlineAlg X Bool) (η : ℕ) :
    ∃ (T : ℕ) (S : Fin T → X × Bool), HasAtMostAnomalies F η S ∧ 2 * η + 1 ≤ mistakes A S := by
  obtain ⟨x, ht, hf⟩ := (shat_succ_iff F 0).1 hF
  obtain ⟨f1, ⟨hf1, hx1⟩⟩ := shat_zero_nonempty _ ht
  obtain ⟨f2, ⟨hf2, hx2⟩⟩ := shat_zero_nonempty _ hf
  obtain ⟨S, h1, h2⟩ := error_path x (2 * η + 1) A
  have hsum : anomalies f1 S + anomalies f2 S = 2 * η + 1 := by
    unfold anomalies
    have e1 : (Finset.univ.filter (fun t : Fin (2*η+1) ↦ f1 (S t).1 ≠ (S t).2)) =
        Finset.univ.filter (fun t : Fin (2*η+1) ↦ true ≠ (S t).2) := by
      apply Finset.filter_congr; intro t _; rw [h1, hx1]
    have e2 : (Finset.univ.filter (fun t : Fin (2*η+1) ↦ f2 (S t).1 ≠ (S t).2)) =
        Finset.univ.filter (fun t : Fin (2*η+1) ↦ ¬ (true ≠ (S t).2)) := by
      apply Finset.filter_congr; intro t _; rw [h1, hx2]
      cases (S t).2 <;> simp
    rw [e1, e2, Finset.card_filter_add_card_filter_not]
    simp
  refine ⟨2 * η + 1, S, ?_, by omega⟩
  by_cases h : anomalies f1 S ≤ η
  · exact ⟨f1, hf1, h⟩
  · exact ⟨f2, hf2, by omega⟩

lemma lower_bound (d : ℕ) : ∀ (F : Set (X → Bool)), Shat F (d+1) → ∀ (A : OnlineAlg X Bool) (η : ℕ),
    ∃ (T : ℕ) (S : Fin T → X × Bool), HasAtMostAnomalies F η S ∧ d + 1 + 2 * η ≤ mistakes A S := by
  induction d with
  | zero =>
    intro F hF A η
    obtain ⟨T, S, h1, h2⟩ := base_case hF A η
    exact ⟨T, S, h1, by omega⟩
  | succ d ih =>
    intro F hF A η
    obtain ⟨x, ht, hf⟩ := (shat_succ_iff F (d+1)).1 hF
    have hG : ∀ b : Bool, Shat {h ∈ F | h x = b} (d+1) := by
      intro b; cases b
      exacts [hf, ht]
    obtain ⟨T, S', ⟨g, hg, hga⟩, hm⟩ :=
      ih _ (hG (!A [] x)) (fun h y => A ((x, !A [] x) :: h) y) η
    refine ⟨T+1, Fin.cons (x, !A [] x) S', ⟨g, hg.1, ?_⟩, ?_⟩
    · rw [anomalies_cons]
      have : g x = !A [] x := hg.2
      simp [this, hga]
    · have key : (if A [] (x, !A [] x).1 ≠ (x, !A [] x).2 then 1 else 0 : ℕ) = 1 := by
        cases h : A [] x <;> simp [h]
      rw [mistakes_cons, key]; omega


lemma versionSpace_append (F : Set (X → Bool)) (P : List (X × Bool)) (s : X × Bool) :
    versionSpace F (P ++ [s]) = versionSpace F P ∩ {h | h s.1 = s.2} := by
  ext h
  simp only [versionSpace, Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_append,
    List.mem_singleton]
  constructor
  · rintro ⟨hF, hh⟩
    exact ⟨⟨hF, fun e he => hh e (Or.inl he)⟩, hh s (Or.inr rfl)⟩
  · rintro ⟨⟨hF, hh⟩, hs⟩
    exact ⟨hF, fun e he => he.elim (hh e) (fun h' => h' ▸ hs)⟩

lemma split_step {V : Set (X → Bool)} (x : X) (l : Bool) (hW : (V ∩ {h | h x = l}).Nonempty)
    (hle : ldimBot (V ∩ {h | h x = l}) ≤ ldimBot (V ∩ {h | h x = !l})) (hT : ldim V ≠ ⊤) :
    ldim (V ∩ {h | h x = l}) + 1 ≤ ldim V := by
  have hW' : (V ∩ {h | h x = !l}).Nonempty := by
    by_contra hn
    have h1 : ldimBot (V ∩ {h | h x = !l}) = ⊥ := by
      unfold ldimBot; rw [if_neg hn]
    have h2 : ldimBot (V ∩ {h | h x = l}) = ((ldim (V ∩ {h | h x = l}) : ℕ∞) : WithBot ℕ∞) := by
      unfold ldimBot; rw [if_pos hW]
    rw [h1, h2] at hle
    exact absurd hle (by simp)
  have hle' : ldim (V ∩ {h | h x = l}) ≤ ldim (V ∩ {h | h x = !l}) := by
    have h1 : ldimBot (V ∩ {h | h x = !l}) =
        ((ldim (V ∩ {h | h x = !l}) : ℕ∞) : WithBot ℕ∞) := by
      unfold ldimBot; rw [if_pos hW']
    have h2 : ldimBot (V ∩ {h | h x = l}) = ((ldim (V ∩ {h | h x = l}) : ℕ∞) : WithBot ℕ∞) := by
      unfold ldimBot; rw [if_pos hW]
    rw [h1, h2] at hle
    exact_mod_cast hle
  have hWV : ldim (V ∩ {h | h x = l}) ≤ ldim V := ldim_mono Set.inter_subset_left
  have hne : ldim (V ∩ {h | h x = l}) ≠ ⊤ := ne_top_of_le_ne_top hT hWV
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
  have s1 : Shat (V ∩ {h | h x = l}) k := ex_shat_of_le x hW k hk.le
  have s2 : Shat (V ∩ {h | h x = !l}) k := ex_shat_of_le x hW' k (by rw [hk]; exact hle')
  have s3 : Shat V (k+1) := by
    refine (shat_succ_iff V k).2 ⟨x, ?_⟩
    cases l
    · exact ⟨s2, s1⟩
    · exact ⟨s1, s2⟩
  have := le_ldim s3
  rw [← hk]
  exact_mod_cast this

lemma soa_mistake_le (F : Set (X → Bool)) (P : List (X × Bool)) (x : X) (l : Bool)
    (h : soa F P x ≠ l) :
    ldimBot (versionSpace F P ∩ {h | h x = l}) ≤ ldimBot (versionSpace F P ∩ {h | h x = !l}) := by
  unfold soa at h
  cases l
  · simp only [ne_eq, decide_eq_false_iff_not, not_not, decide_eq_true_eq] at h
    simpa using h
  · by_cases hh : ldimBot (versionSpace F P ∩ {h | h x = false}) ≤
        ldimBot (versionSpace F P ∩ {h | h x = true})
    · simp [hh] at h
    · have := (not_le.1 hh).le
      simpa using this

lemma soa_bound (F : Set (X → Bool)) : ∀ (n : ℕ) (P : List (X × Bool)) (S : Fin n → X × Bool)
    (f : X → Bool), f ∈ versionSpace F P → (∀ t, f (S t).1 = (S t).2) →
    (mistakes (fun hist y => soa F (P ++ hist) y) S : ℕ∞) ≤ ldim (versionSpace F P) := by
  intro n
  induction n with
  | zero =>
    intro P S f _ _
    simp [mistakes]
  | succ n ih =>
    intro P S f hfP hS
    rw [← Fin.cons_self_tail S]
    have hfP' : f ∈ versionSpace F (P ++ [S 0]) := by
      rw [versionSpace_append]; exact ⟨hfP, hS 0⟩
    have IH := ih (P ++ [S 0]) (Fin.tail S) f hfP' (fun t => hS t.succ)
    rw [mistakes_cons]
    have hfun : (fun (h : List (X × Bool)) (y : X) =>
        (fun hist y => soa F (P ++ hist) y) (S 0 :: h) y) =
        (fun hist y => soa F ((P ++ [S 0]) ++ hist) y) := by
      funext h y; simp
    rw [hfun]
    have hV' : versionSpace F (P ++ [S 0]) = versionSpace F P ∩ {h | h (S 0).1 = (S 0).2} :=
      versionSpace_append F P (S 0)
    have hmono : ldim (versionSpace F (P ++ [S 0])) ≤ ldim (versionSpace F P) := by
      rw [hV']; exact ldim_mono Set.inter_subset_left
    by_cases hT : ldim (versionSpace F P) = ⊤
    · rw [hT]; exact le_top
    by_cases hm : soa F (P ++ []) (S 0).1 ≠ (S 0).2
    · rw [if_pos hm]
      have hm' : soa F P (S 0).1 ≠ (S 0).2 := by simpa using hm
      have hle := soa_mistake_le F P (S 0).1 (S 0).2 hm'
      have hW : (versionSpace F P ∩ {h | h (S 0).1 = (S 0).2}).Nonempty := ⟨f, hfP, hS 0⟩
      have hsp := split_step (S 0).1 (S 0).2 hW hle hT
      rw [← hV'] at hsp
      push_cast
      calc (1 : ℕ∞) + (mistakes (fun hist y => soa F ((P ++ [S 0]) ++ hist) y) (Fin.tail S) : ℕ∞)
          ≤ 1 + ldim (versionSpace F (P ++ [S 0])) := add_le_add le_rfl IH
        _ = ldim (versionSpace F (P ++ [S 0])) + 1 := add_comm _ _
        _ ≤ ldim (versionSpace F P) := hsp
    · rw [if_neg hm]
      push_cast
      simpa using IH.trans hmono

lemma opt_zero_le_ldim (F : Set (X → Bool)) : opt F 0 ≤ ldim F := by
  unfold opt
  refine (iInf_le _ (soa F)).trans ?_
  refine iSup_le fun T => iSup_le fun S => iSup_le fun hS => ?_
  obtain ⟨f, hf, hanom⟩ := hS
  have h0 : anomalies f S = 0 := by omega
  have hS' : ∀ t, f (S t).1 = (S t).2 := by
    intro t
    unfold anomalies at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    have := h0 (Finset.mem_univ t)
    simpa using this
  have hmem : f ∈ versionSpace F [] := ⟨hf, by simp⟩
  have := soa_bound F T [] S f hmem hS'
  have hv : versionSpace F [] = F := by
    ext h; simp [versionSpace]
  rw [hv] at this
  simpa using this

lemma opt_ge {F : Set (X → Bool)} (η : ℕ) (hF1 : Shat F 1) (d : ℕ) (hd : Shat F d) :
    (d : ℕ∞) + 2 * (η : ℕ∞) ≤ opt F η := by
  have key : ∀ e : ℕ, Shat F (e+1) → ((e + 1 : ℕ) : ℕ∞) + 2 * (η : ℕ∞) ≤ opt F η := by
    intro e he
    unfold opt
    refine le_iInf fun A => ?_
    obtain ⟨T, S, h1, h2⟩ := lower_bound e F he A η
    refine le_iSup_of_le T (le_iSup_of_le S (le_iSup_of_le h1 ?_))
    have : ((e + 1 + 2 * η : ℕ) : ℕ∞) ≤ (mistakes A S : ℕ∞) := by exact_mod_cast h2
    push_cast at this ⊢
    exact this
  cases d with
  | zero =>
    have := key 0 hF1
    calc ((0 : ℕ) : ℕ∞) + 2 * (η : ℕ∞) ≤ ((0 + 1 : ℕ) : ℕ∞) + 2 * (η : ℕ∞) :=
          add_le_add (by exact_mod_cast Nat.zero_le _) le_rfl
      _ ≤ _ := this
  | succ e => exact key e hd

theorem theorem_8_1_core {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    opt F 0 + 2 * (η : ℕ∞) ≤ opt F η := by
  obtain ⟨f, hf, g, hg, hfg⟩ := hF
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ g x := by
    by_contra hn
    push_neg at hn
    exact hfg (funext hn)
  have hF1 : Shat F 1 := by
    refine (shat_succ_iff F 0).2 ⟨x, ?_, ?_⟩
    · rw [shat_zero_iff _ x]
      cases hfx : f x
      · refine ⟨g, hg, ?_⟩
        have : g x = true := by
          cases hgx : g x
          · exact absurd (by rw [hfx, hgx]) hx
          · rfl
        exact this
      · exact ⟨f, hf, hfx⟩
    · rw [shat_zero_iff _ x]
      cases hfx : f x
      · exact ⟨f, hf, hfx⟩
      · refine ⟨g, hg, ?_⟩
        cases hgx : g x
        · rfl
        · exact absurd (by rw [hfx, hgx]) hx
  have hne : F.Nonempty := ⟨f, hf⟩
  have h1 : ldim F + 2 * (η : ℕ∞) ≤ opt F η := by
    by_cases hT : ldim F = ⊤
    · have hall : ∀ k : ℕ, (k : ℕ∞) ≤ opt F η := fun k =>
        le_trans le_self_add
          (opt_ge η hF1 k (ex_shat_of_le x hne k (by rw [hT]; exact le_top)))
      have htop : opt F η = ⊤ := by
        by_contra hn
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hn
        have h5 := hall (m+1)
        rw [← hm] at h5
        have h6 : m + 1 ≤ m := by exact_mod_cast h5
        omega
      rw [htop]; exact le_top
    · obtain ⟨K, hK⟩ := ENat.ne_top_iff_exists.1 hT
      have hs : Shat F K := ex_shat_of_le x hne K hK.le
      have := opt_ge η hF1 K hs
      rw [← hK]; exact this
  exact (add_le_add (opt_zero_le_ldim F) le_rfl).trans h1


end Aux
end WeightedMajority.Anomalies

open WeightedMajority.Anomalies
open UnderstandingML

theorem solution {X : Type*} (F : Set (X → Bool)) (hF : F.Nontrivial) (η : ℕ) :
    opt F 0 + 2 * (η : ℕ∞) ≤ opt F η := by
  exact theorem_8_1_core F hF η
