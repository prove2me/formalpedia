-- Prove2me | solution 1 for TalluriMNLFull.Policy.proposition_6_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T10:04:28.12142+00:00
-- url     : https://prove2.me/submissions/b4b3e072-5ba8-48ee-b15e-25baf2a74c65

import Mathlib
import Definitions.Def_TalluriMNLFull_Policy_Frontier
import Definitions.Def_TalluriMNLFull_Policy_Control

set_option autoImplicit false

namespace B70Aux

open RevenueManagement ChoiceRM.Policy TalluriMNLFull.Policy

variable {n : ℕ}

/-! ## MNL formulas -/

lemma mnl_Q (w : Fin n → ℝ) (S : Finset (Fin n)) :
    purchaseProb (ChoiceRM.MNL.mnl w) S = (∑ i ∈ S, w i) / (∑ i ∈ S, w i + 1) := by
  unfold purchaseProb ChoiceRM.MNL.mnl
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun j hj => by simp [hj])

lemma mnl_R (w r : Fin n → ℝ) (S : Finset (Fin n)) :
    expRevenue (ChoiceRM.MNL.mnl w) r S = (∑ i ∈ S, w i * r i) / (∑ i ∈ S, w i + 1) := by
  unfold expRevenue ChoiceRM.MNL.mnl
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [hj, if_true]
  ring

lemma mnl_Q_nonneg (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (S : Finset (Fin n)) :
    0 ≤ purchaseProb (ChoiceRM.MNL.mnl w) S := by
  rw [mnl_Q]
  have : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  positivity

lemma mnl_Q_le_one (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (S : Finset (Fin n)) :
    purchaseProb (ChoiceRM.MNL.mnl w) S ≤ 1 := by
  rw [mnl_Q]
  have : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  rw [div_le_one (by linarith)]
  linarith

lemma mnl_Q_mono (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) {A B : Finset (Fin n)} (hsub : A ⊆ B) :
    purchaseProb (ChoiceRM.MNL.mnl w) A ≤ purchaseProb (ChoiceRM.MNL.mnl w) B := by
  rw [mnl_Q, mnl_Q]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hw i).le)
  have h0 : 0 ≤ ∑ i ∈ A, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-! ## Domination by a two-set mixture -/

lemma two_sum (A B : Finset (Fin n)) (hAB : A ≠ B) (θ : ℝ) (F : Finset (Fin n) → ℝ) :
    ∑ S, (if S = B then θ else if S = A then 1 - θ else 0) * F S =
      θ * F B + (1 - θ) * F A := by
  have h : ∀ S : Finset (Fin n), (if S = B then θ else if S = A then 1 - θ else 0) * F S =
      (if S = B then θ * F B else 0) + (if S = A then (1 - θ) * F A else 0) := by
    intro S
    by_cases hB : S = B
    · subst hB
      simp [Ne.symm hAB]
    · by_cases hA : S = A
      · subst hA
        simp [hB]
      · simp [hA, hB]
  rw [Finset.sum_congr rfl (fun S _ => h S), Finset.sum_add_distrib]
  simp

lemma alg (WA WB NA NB l D : ℝ) (hA : 0 ≤ WA) (hB : 0 ≤ WB) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hDdef : D = l * WB + (1 - l) * WA + 1) :
    0 ≤ l * (WB + 1) / D ∧ 0 ≤ 1 - l * (WB + 1) / D ∧
    l * (WB + 1) / D * (WB / (WB + 1)) + (1 - l * (WB + 1) / D) * (WA / (WA + 1)) =
      (l * WB + (1 - l) * WA) / D ∧
    l * (WB + 1) / D * (NB / (WB + 1)) + (1 - l * (WB + 1) / D) * (NA / (WA + 1)) =
      (l * NB + (1 - l) * NA) / D := by
  have hlA : 0 ≤ (1 - l) * WA := mul_nonneg (by linarith) hA
  have hlB : 0 ≤ l * WB := mul_nonneg hl0 hB
  have hD : 0 < D := by rw [hDdef]; linarith
  have hA1 : WA + 1 ≠ 0 := by linarith
  have hB1 : WB + 1 ≠ 0 := by linarith
  refine ⟨div_nonneg (mul_nonneg hl0 (by linarith)) hD.le, ?_, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hD, hDdef]
    nlinarith
  · subst hDdef
    field_simp
    ring
  · subst hDdef
    field_simp
    ring

lemma dom_of_mix (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (T A B : Finset (Fin n)) (hAB : A ≠ B)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hW : ∑ i ∈ T, w i = l * ∑ i ∈ B, w i + (1 - l) * ∑ i ∈ A, w i)
    (hN : ∑ i ∈ T, w i * r i < l * ∑ i ∈ B, w i * r i + (1 - l) * ∑ i ∈ A, w i * r i) :
    IsDominated (ChoiceRM.MNL.mnl w) r T := by
  have hA : 0 ≤ ∑ i ∈ A, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hB : 0 ≤ ∑ i ∈ B, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hT : 0 ≤ ∑ i ∈ T, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  obtain ⟨h0, h1, hq, hrv⟩ := alg (∑ i ∈ A, w i) (∑ i ∈ B, w i) (∑ i ∈ A, w i * r i)
    (∑ i ∈ B, w i * r i) l (∑ i ∈ T, w i + 1) hA hB hl0 hl1 (by rw [hW])
  refine ⟨fun S => if S = B then l * (∑ i ∈ B, w i + 1) / (∑ i ∈ T, w i + 1)
      else if S = A then 1 - l * (∑ i ∈ B, w i + 1) / (∑ i ∈ T, w i + 1) else 0,
    ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · intro S
    dsimp only
    split_ifs
    · exact h0
    · exact h1
    · exact le_refl 0
  · have := two_sum A B hAB (l * (∑ i ∈ B, w i + 1) / (∑ i ∈ T, w i + 1)) (fun _ => 1)
    simp only [mul_one] at this
    linarith
  · rw [two_sum A B hAB _ (purchaseProb (ChoiceRM.MNL.mnl w)), mnl_Q w B, mnl_Q w A, mnl_Q w T,
      hq, ← hW]
  · rw [two_sum A B hAB _ (expRevenue (ChoiceRM.MNL.mnl w) r), mnl_R w r B, mnl_R w r A,
      mnl_R w r T, hrv]
    exact (div_lt_div_iff_of_pos_right (by linarith)).2 hN

lemma dom_of_inv (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (U : Finset (Fin n)) (i j : Fin n)
    (hiU : i ∉ U) (hjU : j ∉ U) (hij : i ≠ j) (hr : r j < r i) :
    IsDominated (ChoiceRM.MNL.mnl w) r (insert j U) := by
  have hji : j ∉ insert i U := by simp [hjU, Ne.symm hij]
  have hwi := hw i
  have hwj := hw j
  rcases le_or_gt (w j) (w i) with hle | hlt
  · refine dom_of_mix w r hw (insert j U) U (insert i U)
      (fun h => hiU (h ▸ Finset.mem_insert_self i U)) (w j / w i)
      (div_nonneg hwj.le hwi.le) ((div_le_one hwi).2 hle) ?_ ?_
    · rw [Finset.sum_insert hjU, Finset.sum_insert hiU]
      field_simp
      ring
    · rw [Finset.sum_insert hjU, Finset.sum_insert hiU]
      have e : w j / w i * (w i * r i + ∑ x ∈ U, w x * r x) + (1 - w j / w i) * ∑ x ∈ U, w x * r x
          = w j * r i + ∑ x ∈ U, w x * r x := by
        field_simp
        ring
      rw [e]
      nlinarith [mul_lt_mul_of_pos_left hr hwj]
  · refine dom_of_mix w r hw (insert j U) (insert i U) (insert j (insert i U))
      (fun h => hji (h ▸ Finset.mem_insert_self j (insert i U))) ((w j - w i) / w j)
      (div_nonneg (by linarith) hwj.le) ((div_le_one hwj).2 (by linarith)) ?_ ?_
    · rw [Finset.sum_insert hjU, Finset.sum_insert hji, Finset.sum_insert hiU]
      field_simp
      ring
    · rw [Finset.sum_insert hjU, Finset.sum_insert hji, Finset.sum_insert hiU]
      have e : (w j - w i) / w j * (w j * r j + (w i * r i + ∑ x ∈ U, w x * r x)) +
          (1 - (w j - w i) / w j) * (w i * r i + ∑ x ∈ U, w x * r x)
          = (w j - w i) * r j + w i * r i + ∑ x ∈ U, w x * r x := by
        field_simp
        ring
      rw [e]
      nlinarith [mul_lt_mul_of_pos_left hr hwi]

lemma nfi_of_nondom (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (S : Finset (Fin n))
    (hS : ChoiceRM.Policy.IsNondominated (ChoiceRM.MNL.mnl w) r S) :
    NoStrictFareInversion r S := by
  intro i hi j hj
  by_contra hlt
  push_neg at hlt
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hd := dom_of_inv w r hw (S.erase j) i j (fun h => hi (Finset.mem_of_mem_erase h))
    (by simp) hij hlt
  rw [Finset.insert_erase hj] at hd
  exact hS hd

/-! ## Static stage problem: revenue-ordered prefixes -/

/-- `R(S) - Q(S) v` for the MNL model. -/
noncomputable def fv (w r : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) : ℝ :=
  expRevenue (ChoiceRM.MNL.mnl w) r S - purchaseProb (ChoiceRM.MNL.mnl w) S * v

lemma fv_eq (w r : Fin n → ℝ) (v : ℝ) (S : Finset (Fin n)) :
    fv w r v S = (∑ i ∈ S, w i * r i - v * ∑ i ∈ S, w i) / (∑ i ∈ S, w i + 1) := by
  unfold fv
  rw [mnl_Q, mnl_R]
  ring

lemma sum_g (w r : Fin n → ℝ) (c : ℝ) (S : Finset (Fin n)) :
    ∑ j ∈ S, w j * (r j - c) = ∑ j ∈ S, w j * r j - c * ∑ j ∈ S, w j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma sum_eq_ite (S : Finset (Fin n)) (g : Fin n → ℝ) :
    ∑ j ∈ S, g j = ∑ j, if j ∈ S then g j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

lemma prefix_opt (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (horder : Antitone r) (v : ℝ) :
    ∃ k ≤ n, ∀ S : Finset (Fin n), fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n k) := by
  classical
  obtain ⟨Sm, -, hSm⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
    (fv w r v) Finset.univ_nonempty
  obtain ⟨z, hz⟩ : ∃ z, fv w r v Sm = z := ⟨_, rfl⟩
  let Pk : ℕ → Prop := fun k => ∀ j : Fin n, j.val < k → v + z < r j
  have hP0 : Pk 0 := fun j h => absurd h (Nat.not_lt_zero _)
  obtain ⟨k, hkdef⟩ : ∃ k, Nat.findGreatest Pk n = k := ⟨_, rfl⟩
  have hkn : k ≤ n := by rw [← hkdef]; exact Nat.findGreatest_le n
  have hkP : Pk k := by rw [← hkdef]; exact Nat.findGreatest_spec (Nat.zero_le n) hP0
  have hA : ∀ j : Fin n, j ∈ ChoiceRM.MNL.complete n k ↔ v + z < r j := by
    intro j
    simp only [ChoiceRM.MNL.complete, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hkP j
    · intro hj
      by_contra hcon
      push_neg at hcon
      have hP : Pk (j.val + 1) := by
        intro i hi
        have hij : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
        exact lt_of_lt_of_le hj (horder hij)
      have := Nat.le_findGreatest (show j.val + 1 ≤ n from j.isLt) hP
      rw [hkdef] at this
      omega
  refine ⟨k, hkn, ?_⟩
  intro S
  have hS := hSm S (Finset.mem_univ S)
  rw [hz] at hS
  have hsum : ∑ j ∈ Sm, w j * (r j - (v + z)) ≤
      ∑ j ∈ ChoiceRM.MNL.complete n k, w j * (r j - (v + z)) := by
    rw [sum_eq_ite Sm, sum_eq_ite (ChoiceRM.MNL.complete n k)]
    apply Finset.sum_le_sum
    intro j _
    have hwj := hw j
    by_cases h1 : j ∈ Sm
    · by_cases h2 : v + z < r j
      · rw [if_pos h1, if_pos ((hA j).2 h2)]
      · rw [if_pos h1, if_neg (fun h => h2 ((hA j).1 h))]
        push_neg at h2
        nlinarith
    · rw [if_neg h1]
      by_cases h2 : v + z < r j
      · rw [if_pos ((hA j).2 h2)]
        nlinarith
      · rw [if_neg (fun h => h2 ((hA j).1 h))]
  have e1 := sum_g w r (v + z) Sm
  have e2 := sum_g w r (v + z) (ChoiceRM.MNL.complete n k)
  have hWm : 0 ≤ ∑ i ∈ Sm, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hWA : 0 ≤ ∑ i ∈ ChoiceRM.MNL.complete n k, w i :=
    Finset.sum_nonneg (fun i _ => (hw i).le)
  rw [fv_eq] at hz
  have hzS := (eq_div_iff (show ∑ i ∈ Sm, w i + 1 ≠ 0 by linarith)).1 hz.symm
  refine le_trans hS ?_
  rw [fv_eq, le_div_iff₀ (by linarith)]
  nlinarith

open Classical in
/-- The largest prefix index that maximizes `R - Q v` over all offer sets. -/
noncomputable def kstar (w r : Fin n → ℝ) (v : ℝ) : ℕ :=
  Nat.findGreatest
    (fun k => ∀ S : Finset (Fin n), fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n k)) n

lemma kstar_le (w r : Fin n → ℝ) (v : ℝ) : kstar w r v ≤ n := by
  unfold kstar
  exact Nat.findGreatest_le n

lemma kstar_spec (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (horder : Antitone r) (v : ℝ) :
    ∀ S, fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n (kstar w r v)) := by
  obtain ⟨k, hk, hP⟩ := prefix_opt w r hw horder v
  unfold kstar
  exact Nat.findGreatest_spec
    (P := fun k => ∀ S : Finset (Fin n), fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n k)) hk hP

lemma le_kstar (w r : Fin n → ℝ) (v : ℝ) {k : ℕ} (hk : k ≤ n)
    (hP : ∀ S, fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n k)) : k ≤ kstar w r v := by
  unfold kstar
  exact Nat.le_findGreatest hk hP

lemma complete_mono {k k' : ℕ} (h : k ≤ k') :
    ChoiceRM.MNL.complete n k ⊆ ChoiceRM.MNL.complete n k' := by
  intro j hj
  simp only [ChoiceRM.MNL.complete, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  omega

lemma kstar_anti (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (horder : Antitone r) {v v' : ℝ}
    (hvv : v ≤ v') : kstar w r v' ≤ kstar w r v := by
  have s' := kstar_spec w r hw horder v'
  have s := kstar_spec w r hw horder v
  by_contra hlt
  push_neg at hlt
  have hQ := mnl_Q_mono w hw (complete_mono (n := n) hlt.le)
  have hP : ∀ S, fv w r v S ≤ fv w r v (ChoiceRM.MNL.complete n (kstar w r v')) := by
    intro S
    have h1 := s S
    have h2 := s (ChoiceRM.MNL.complete n (kstar w r v'))
    have h3 := s' (ChoiceRM.MNL.complete n (kstar w r v))
    have h4 := mul_le_mul_of_nonneg_left hvv (sub_nonneg.2 hQ)
    unfold fv at h1 h2 h3 ⊢
    linarith
  have := le_kstar w r v (kstar_le w r v') hP
  omega

/-! ## Bellman recursion: concavity, policy value, randomized rules -/

noncomputable def hfun (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (v : ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty
    (fun S => a * (expRevenue P r S - purchaseProb P S * v))

lemma le_hfun (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (v : ℝ)
    (S : Finset (Fin n)) : a * (expRevenue P r S - purchaseProb P S * v) ≤ hfun a P r v :=
  Finset.le_sup'_of_le _ (Finset.mem_univ S) le_rfl

lemma hfun_le (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (v B : ℝ)
    (h : ∀ S, a * (expRevenue P r S - purchaseProb P S * v) ≤ B) : hfun a P r v ≤ B :=
  Finset.sup'_le _ _ (fun S _ => h S)

lemma hfun_nonneg (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (v : ℝ) :
    0 ≤ hfun a P r v := by
  refine le_trans ?_ (le_hfun a P r v ∅)
  simp [expRevenue, purchaseProb]

lemma hfun_anti (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (hQ0 : ∀ S, 0 ≤ purchaseProb P S) {u m : ℝ} (hum : u ≤ m) :
    hfun a P r m ≤ hfun a P r u := by
  apply hfun_le
  intro S
  have h1 := le_hfun a P r u S
  have h2 := mul_le_mul_of_nonneg_left hum (hQ0 S)
  have h3 := mul_le_mul_of_nonneg_left
    (show expRevenue P r S - purchaseProb P S * m ≤ expRevenue P r S - purchaseProb P S * u by
      linarith) ha0
  linarith

lemma hfun_lip (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hQ0 : ∀ S, 0 ≤ purchaseProb P S) (hQ1 : ∀ S, purchaseProb P S ≤ 1)
    {u m : ℝ} (hum : u ≤ m) : hfun a P r u ≤ hfun a P r m + (m - u) := by
  apply hfun_le
  intro S
  have h1 := le_hfun a P r m S
  have h2 : a * purchaseProb P S ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (hQ1 S) ha0
    linarith
  have h4 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hum)
  linarith

lemma V_zero_t (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (x : ℕ) :
    V a P r 0 x = 0 := by
  simp [V, choiceValueGo]

lemma V_x0 (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (t : ℕ) :
    V a P r t 0 = 0 := by
  cases t <;> simp [V, choiceValueGo]

lemma V_succ (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (t x : ℕ) :
    V a P r (t + 1) (x + 1) =
      hfun a P r (V a P r t (x + 1) - V a P r t x) + V a P r t (x + 1) := by
  rfl

lemma V_concave (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hQ0 : ∀ S, 0 ≤ purchaseProb P S) (hQ1 : ∀ S, purchaseProb P S ≤ 1) :
    ∀ t y : ℕ, V a P r t (y + 1 + 1) - V a P r t (y + 1) ≤ V a P r t (y + 1) - V a P r t y := by
  intro t
  induction t with
  | zero => intro y; simp [V_zero_t]
  | succ t ih =>
    intro y
    rcases y with _ | z
    · have h1 := ih 0
      rw [V_succ a P r t (0 + 1), V_succ a P r t 0, V_x0 a P r (t + 1)]
      have hl := hfun_lip a P r ha0 ha1 hQ0 hQ1 h1
      have hn := hfun_nonneg a P r (V a P r t (0 + 1) - V a P r t 0)
      have h0 := V_x0 a P r t
      linarith
    · have hu := ih (z + 1)
      have hm := ih z
      rw [V_succ a P r t (z + 1 + 1), V_succ a P r t (z + 1), V_succ a P r t z]
      have hl := hfun_lip a P r ha0 ha1 hQ0 hQ1 hu
      have ha := hfun_anti a P r ha0 hQ0 hm
      linarith

lemma dV_step (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hQ0 : ∀ S, 0 ≤ purchaseProb P S) (hQ1 : ∀ S, purchaseProb P S ≤ 1)
    (s y : ℕ) : deltaV a P r s (y + 1 + 1) ≤ deltaV a P r s (y + 1) := by
  have := V_concave a P r ha0 ha1 hQ0 hQ1 s y
  simp only [deltaV, Nat.add_sub_cancel]
  exact this

lemma dV_anti (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hQ0 : ∀ S, 0 ≤ purchaseProb P S) (hQ1 : ∀ S, purchaseProb P S ≤ 1)
    (s : ℕ) {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) : deltaV a P r s y ≤ deltaV a P r s x := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_refl _
  | succ y hxy ih =>
    obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    exact le_trans (dV_step a P r ha0 ha1 hQ0 hQ1 s y') ih

lemma stage_eq (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (t x : ℕ)
    (S : Finset (Fin n)) :
    stageObj a P r (t + 1) (x + 1) S =
      a * (expRevenue P r S - purchaseProb P S * (V a P r t (x + 1) - V a P r t x)) := by
  simp only [stageObj, deltaV, Nat.add_sub_cancel]

lemma J_eq_V (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (π : MarkovPolicy n)
    (hopt : ∀ t x, IsOptimalOffer a P r (t + 1) (x + 1) (π (t + 1) (x + 1))) :
    ∀ t x, policyRevenue a P r π t x = V a P r t x := by
  intro t
  induction t with
  | zero => intro x; simp [policyRevenue, V_zero_t]
  | succ t ih =>
    intro x
    rcases x with _ | x
    · simp [policyRevenue, V_x0]
    · have hmax : hfun a P r (V a P r t (x + 1) - V a P r t x) =
          a * (expRevenue P r (π (t + 1) (x + 1)) -
            purchaseProb P (π (t + 1) (x + 1)) * (V a P r t (x + 1) - V a P r t x)) := by
        apply le_antisymm
        · apply hfun_le
          intro S
          have := hopt t x S
          rw [stage_eq, stage_eq] at this
          exact this
        · exact le_hfun _ _ _ _ _
      rw [V_succ, hmax]
      simp only [policyRevenue]
      rw [ih x, ih (x + 1)]
      ring

lemma rand_le_V (a : ℝ) (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hQ0 : ∀ S, 0 ≤ purchaseProb P S) (hQ1 : ∀ S, purchaseProb P S ≤ 1)
    (μ : RandomizedPolicy n) (hμ0 : ∀ t x S, 0 ≤ μ t x S) (hμ1 : ∀ t x, ∑ S, μ t x S = 1) :
    ∀ t x, randomizedRevenue a P r μ t x ≤ V a P r t x := by
  intro t
  induction t with
  | zero => intro x; simp [randomizedRevenue, V_zero_t]
  | succ t ih =>
    intro x
    rcases x with _ | x
    · simp [randomizedRevenue, V_x0]
    · rw [V_succ]
      simp only [randomizedRevenue]
      calc _ ≤ ∑ S, μ (t + 1) (x + 1) S *
            (hfun a P r (V a P r t (x + 1) - V a P r t x) + V a P r t (x + 1)) := by
            apply Finset.sum_le_sum
            intro S _
            apply mul_le_mul_of_nonneg_left _ (hμ0 _ _ S)
            have h1 := ih x
            have h2 := ih (x + 1)
            have hq0 : 0 ≤ a * purchaseProb P S := mul_nonneg ha0 (hQ0 S)
            have hq1 : a * purchaseProb P S ≤ 1 := by
              have := mul_le_mul_of_nonneg_left (hQ1 S) ha0
              linarith
            have e1 := mul_le_mul_of_nonneg_left h1 hq0
            have e2 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hq1)
            have e3 := le_hfun a P r (V a P r t (x + 1) - V a P r t x) S
            linarith
        _ = _ := by rw [← Finset.sum_mul, hμ1, one_mul]

/-! ## The nested policy -/

noncomputable def kfun (a : ℝ) (w r : Fin n → ℝ) (t x : ℕ) : Fin (n + 1) :=
  if x = 0 then 0
  else ⟨kstar w r (deltaV a (ChoiceRM.MNL.mnl w) r (t - 1) x),
    Nat.lt_succ_of_le (kstar_le w r _)⟩

lemma kfun_zero (a : ℝ) (w r : Fin n → ℝ) (t : ℕ) : (kfun a w r t 0).val = 0 := by
  simp [kfun]

lemma kfun_opt (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (horder : Antitone r) (a : ℝ)
    (ha0 : 0 ≤ a) (t x : ℕ) (hx : 1 ≤ x) :
    IsOptimalOffer a (ChoiceRM.MNL.mnl w) r t x (prefixPolicy (kfun a w r) t x) := by
  have hx0 : x ≠ 0 := by omega
  unfold IsOptimalOffer stageObj prefixPolicy kfun
  intro S'
  rw [if_neg hx0]
  exact mul_le_mul_of_nonneg_left (kstar_spec w r hw horder _ S') ha0

lemma kfun_mono (w r : Fin n → ℝ) (hw : ∀ j, 0 < w j) (horder : Antitone r) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (t x y : ℕ) (hxy : x ≤ y) :
    (kfun a w r t x).val ≤ (kfun a w r t y).val := by
  by_cases hx : x = 0
  · simp [kfun, hx]
  · have hy : y ≠ 0 := by omega
    simp only [kfun, hx, hy, if_false]
    exact kstar_anti w r hw horder
      (dV_anti a _ r ha0 ha1 (mnl_Q_nonneg w hw) (mnl_Q_le_one w hw) (t - 1) (by omega) hxy)

end B70Aux

open TalluriMNLFull.Policy in
theorem solution {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (horder : Antitone r)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (H C : ℕ) :
    (∀ S : Finset (Fin n), ChoiceRM.Policy.IsNondominated (ChoiceRM.MNL.mnl w) r S →
      NoStrictFareInversion r S) ∧
    ∃ k : ℕ → ℕ → Fin (n + 1),
      (∀ t, (k t 0).val = 0) ∧
      IsAdmissible (prefixPolicy k) ∧
      IsFareOrderNested H C (prefixPolicy k) k ∧
      (∀ t x, t ≤ H → x ≤ C →
        policyRevenue a (ChoiceRM.MNL.mnl w) r (prefixPolicy k) t x =
          ChoiceRM.Policy.V a (ChoiceRM.MNL.mnl w) r t x) ∧
      (∀ t x, 1 ≤ t → t ≤ H → 1 ≤ x → x ≤ C →
        ChoiceRM.Policy.IsOptimalOffer a (ChoiceRM.MNL.mnl w) r t x (prefixPolicy k t x)) ∧
      (∀ μ : RandomizedPolicy n, IsRandomizedPolicy μ →
        ∀ t x, t ≤ H → x ≤ C →
          randomizedRevenue a (ChoiceRM.MNL.mnl w) r μ t x ≤
            policyRevenue a (ChoiceRM.MNL.mnl w) r (prefixPolicy k) t x) := by
  have hQ0 := B70Aux.mnl_Q_nonneg w hw
  have hQ1 := B70Aux.mnl_Q_le_one w hw
  have hopt := B70Aux.kfun_opt w r hw horder a ha0
  have hJ := B70Aux.J_eq_V a (ChoiceRM.MNL.mnl w) r (prefixPolicy (B70Aux.kfun a w r))
    (fun t x => hopt (t + 1) (x + 1) (Nat.succ_pos x))
  refine ⟨fun S hS => B70Aux.nfi_of_nondom w r hw S hS, B70Aux.kfun a w r,
    fun t => B70Aux.kfun_zero a w r t, ?_, ?_, fun t x _ _ => hJ t x,
    fun t x _ _ hx _ => hopt t x hx, ?_⟩
  · intro t
    show ChoiceRM.MNL.complete n (B70Aux.kfun a w r t 0).val = ∅
    rw [B70Aux.kfun_zero]
    ext j
    simp [ChoiceRM.MNL.complete]
  · refine ⟨fun t x _ _ => rfl, ?_⟩
    intro t _ x y hxy _
    exact B70Aux.kfun_mono w r hw horder a ha0 ha1 t x y hxy
  · intro μ hμ t x _ _
    obtain ⟨hμ0, hμ1, -⟩ := hμ
    rw [hJ]
    exact B70Aux.rand_le_V a _ r ha0 ha1 hQ0 hQ1 μ hμ0 hμ1 t x
