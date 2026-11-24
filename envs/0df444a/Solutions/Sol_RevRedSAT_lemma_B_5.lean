-- Prove2me | solution 1 for RevRedSAT.lemma_B_5
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:18:48.633857+00:00
-- url     : https://prove2.me/submissions/0c2be11d-5355-47e4-96ec-2ae46dad0e5b

import Mathlib
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSATB5Aux

open RevRedSAT

lemma aval_eq (d j : ℕ) : Aval d j = 2 * d * (2 : ℝ) ^ j := by
  unfold Aval deltaOf
  rw [div_inv_eq_mul]

lemma aval_ge (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) : 4 * (d : ℝ) ≤ Aval d j ∧ 16 ≤ Aval d j := by
  rw [aval_eq]
  have h4 : (4 : ℝ) ≤ 2 ^ j := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  constructor <;> nlinarith

lemma tp_mono (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {p q : ℕ} (hpq : p ≤ q) :
    tp d j p ≤ tp d j q := by
  unfold tp
  have hA := (aval_ge d j hd hj).2
  have hd' : (0 : ℝ) < 4 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  apply div_le_div_of_nonneg_right _ hd'.le
  exact pow_le_pow_right₀ (by linarith) (by omega)

lemma one_le_tp (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {p : ℕ} (hp : 1 ≤ p) : 1 ≤ tp d j p := by
  have h := tp_mono d j hd hj hp
  refine le_trans ?_ h
  unfold tp
  obtain ⟨h4, h16⟩ := aval_ge d j hd hj
  have hd' : (0 : ℝ) < 4 * d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [le_div_iff₀ hd', one_mul]
  have := pow_le_pow_right₀ (show (1 : ℝ) ≤ Aval d j by linarith) (show 1 ≤ 4 * 1 by norm_num)
  rw [pow_one] at this
  linarith

/-- `w_s · t_{s-1} = 1/(8d)` for `s ≥ 1`. -/
lemma ws_mul_tp (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {s : ℕ} (hs : 1 ≤ s) :
    ws d j s * tp d j (s - 1) = 1 / (8 * d) := by
  unfold ws tp
  have hA : Aval d j ≠ 0 := by have := (aval_ge d j hd hj).2; linarith
  have hd' : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hz : Aval d j ^ ((4 : ℤ) - 4 * s) * Aval d j ^ (4 * (s - 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hA]
    have : ((4 : ℤ) - 4 * (s : ℤ)) + ((4 * (s - 1) : ℕ) : ℤ) = 0 := by
      rw [Nat.cast_mul, Nat.cast_sub hs]; push_cast; ring
    rw [this, zpow_zero]
  calc 1 / 2 * Aval d j ^ ((4 : ℤ) - 4 * s) * (Aval d j ^ (4 * (s - 1)) / (4 * d))
      = 1 / 2 * (Aval d j ^ ((4 : ℤ) - 4 * s) * Aval d j ^ (4 * (s - 1))) / (4 * d) := by ring
    _ = 1 / (8 * d) := by rw [hz]; field_simp; ring

lemma ws_nonneg (d j s : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) : 0 ≤ ws d j s := by
  unfold ws
  have := (aval_ge d j hd hj).2
  have : 0 < Aval d j := by linarith
  positivity

lemma sup_spec (d : ℕ) (Q : ℕ → Prop) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t ∈ Finset.Icc 1 d ∧ ∀ s ∈ Finset.Icc 1 t, Q s) :
    T.sup id ≤ d ∧ ∀ s ∈ Finset.Icc 1 (T.sup id), Q s := by
  rcases T.eq_empty_or_nonempty with h | h
  · subst h; simp
  · obtain ⟨t, ht, he⟩ := Finset.exists_mem_eq_sup T h id
    rw [he]
    obtain ⟨h1, h2⟩ := hT t ht
    exact ⟨(Finset.mem_Icc.mp h1).2, h2⟩

lemma mem_filter_any {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p inst s) : a ∈ s ∧ p a :=
  Finset.mem_filter.mp h

lemma tau_spec {n : ℕ} (d j : ℕ) (F : Finset (Finset (Fin n))) :
    tau d j F ≤ d ∧ ∀ s ∈ Finset.Icc 1 (tau d j F), AlmostSparseLayer d j F s := by
  unfold tau
  refine sup_spec d (fun s => AlmostSparseLayer d j F s) _ ?_
  intro t ht
  exact mem_filter_any _ _ _ _ ht

lemma filter_mem_of {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α)
    (h1 : a ∈ s) (h2 : p a) : a ∈ @Finset.filter α p inst s :=
  Finset.mem_filter.mpr ⟨h1, h2⟩

lemma le_tau {n : ℕ} (d j : ℕ) (G : Finset (Finset (Fin n))) (t : ℕ) (ht : t ∈ Finset.Icc 1 d)
    (h : ∀ s ∈ Finset.Icc 1 t, AlmostSparseLayer d j G s) : t ≤ tau d j G := by
  unfold tau
  exact Finset.le_sup (f := id) (filter_mem_of _ _ _ _ ht h)

lemma mem_reduceFam {n : ℕ} (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    S ∈ reduceFam F ↔ S ∈ F ∧ ¬ ∃ T ∈ F, T ⊂ S := by
  unfold reduceFam
  exact Finset.mem_filter

lemma mem_layer {n : ℕ} (F : Finset (Finset (Fin n))) (s : ℕ) (S : Finset (Fin n)) :
    S ∈ layer F s ↔ S ∈ F ∧ S.card = s := by
  unfold layer
  exact Finset.mem_filter

lemma noFlower_mono {n : ℕ} {A B : Finset (Finset (Fin n))} (hAB : A ⊆ B) (s : ℕ)
    (θ : ℕ → ℝ) (h : NoFlowerAtLeast B s θ) : NoFlowerAtLeast A s θ := by
  intro Z hZ
  obtain ⟨h1, h2, h3, h4⟩ := hZ
  apply h Z
  refine ⟨?_, h2, h3, h4⟩
  intro S hS
  have := (mem_layer _ _ _).mp (h1 hS)
  exact (mem_layer _ _ _).mpr ⟨hAB this.1, this.2⟩

/-- `w_s · t_{s-h} = w_h / (4d)` for `h ≤ s`. -/
lemma ws_mul_tp_sub (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) {h s : ℕ} (hhs : h ≤ s) :
    ws d j s * tp d j (s - h) = ws d j h / (4 * d) := by
  unfold ws tp
  have hA : Aval d j ≠ 0 := by have := (aval_ge d j hd hj).2; linarith
  have hz : Aval d j ^ ((4 : ℤ) - 4 * s) * Aval d j ^ (4 * (s - h)) =
      Aval d j ^ ((4 : ℤ) - 4 * h) := by
    rw [← zpow_natCast, ← zpow_add₀ hA]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub hhs]; push_cast; ring
  calc 1 / 2 * Aval d j ^ ((4 : ℤ) - 4 * s) * (Aval d j ^ (4 * (s - h)) / (4 * d))
      = 1 / 2 * (Aval d j ^ ((4 : ℤ) - 4 * s) * Aval d j ^ (4 * (s - h))) / (4 * d) := by ring
    _ = 1 / 2 * Aval d j ^ ((4 : ℤ) - 4 * h) / (4 * d) := by rw [hz]

/-- In an almost sparse layer `F_s`, at most `2 t_{s-h}` sets contain a given `h`-set, `h < s`. -/
lemma star_bound {n : ℕ} (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (F : Finset (Finset (Fin n)))
    (h s : ℕ) (hh : 1 ≤ h) (hhs : h < s) (hA : AlmostSparseLayer d j F s)
    (T : Finset (Fin n)) (hT : T.card = h) :
    ((((layer F s).filter fun S => T ⊆ S).card : ℕ) : ℝ) ≤ 2 * tp d j (s - h) := by
  classical
  set Gs := (layer F s).filter fun S => T ⊆ S with hGs
  have memGs : ∀ S ∈ Gs, S ∈ F ∧ T ⊆ S ∧ S.card = s := by
    intro S hS
    rw [hGs, Finset.mem_filter] at hS
    have h1 := (mem_layer _ _ _).mp hS.1
    exact ⟨h1.1, hS.2, h1.2⟩
  have ht1 := one_le_tp d j hd hj (show 1 ≤ s - h by omega)
  by_cases hc : Gs.card ≤ 1
  · have : ((Gs.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
    linarith
  · push Not at hc
    obtain ⟨S, hS, S', hS', hSS⟩ := Finset.one_lt_card.mp hc
    obtain ⟨_, _, hcS⟩ := memGs S hS
    obtain ⟨_, _, hcS'⟩ := memGs S' hS'
    have hcoreS : core Gs ⊆ S := by
      unfold core; exact Finset.inf_le (f := id) hS
    have hcoreS' : core Gs ⊆ S' := by
      unfold core; exact Finset.inf_le (f := id) hS'
    have hTcore : T ⊆ core Gs := by
      unfold core
      exact Finset.le_inf fun V hV => (memGs V hV).2.1
    have hcard_lt : (core Gs).card < s := by
      have hsub : core Gs ⊆ S ∩ S' := Finset.subset_inter hcoreS hcoreS'
      have hlt : (S ∩ S').card < S.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_left, fun h => hSS ?_⟩
        have hST' : S ⊆ S' := fun x hx => (Finset.mem_inter.mp (h hx)).2
        exact Finset.eq_of_subset_of_card_le hST' (by omega)
      have := Finset.card_le_card hsub
      omega
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hcore_ge : h ≤ (core Gs).card := hT ▸ Finset.card_le_card hTcore
    have hflower : IsFlower (layer F s) s Gs := by
      refine ⟨?_, ⟨S, hS⟩, hTne.mono hTcore, hcard_lt⟩
      intro V hV
      obtain ⟨hVF, _, hVc⟩ := memGs V hV
      exact (mem_layer _ _ _).mpr ⟨(mem_layer _ _ _).mpr ⟨hVF, hVc⟩, hVc⟩
    have hlt := hA Gs hflower
    have hmono : tp d j (s - (core Gs).card) ≤ tp d j (s - h) :=
      tp_mono d j hd hj (by omega)
    linarith

end RevRedSATB5Aux

open RevRedSAT RevRedSATB5Aux in
theorem solution (d j n k h : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hk : 0 < k)
    (F : Finset (Finset (Fin n))) (hrank : ∀ S ∈ F, S.card ≤ d) (hne : ∀ S ∈ F, S.Nonempty)
    (hred : IsReduced F) (hh₁ : 1 ≤ h) (hh : h ≤ tau d j F)
    (Q : Finset (Finset (Fin n))) (hQ : ∀ S ∈ Q, S.card = h)
    (hQF : ∀ S ∈ F, ∀ T ∈ Q, ¬ S ⊆ T)
    (has : NoFlowerAtLeast (layer F h ∪ Q) h (fun p => 2 * tp d j p)) :
    mu d j k (reduceFam (F ∪ Q)) ≤ mu d j k F - ws d j h / 2 * Q.card := by
  classical
  set G := reduceFam (F ∪ Q) with hGdef
  have hredF : ∀ S ∈ F, ¬ ∃ T ∈ F, T ⊂ S := by
    intro S hS
    have : S ∈ reduceFam F := by unfold RevRedSAT.IsReduced at hred; rw [hred]; exact hS
    exact ((mem_reduceFam _ _).mp this).2
  have hQnotF : ∀ T ∈ Q, T ∉ F := fun T hT hTF => hQF T hTF T hT subset_rfl
  have hFG : ∀ S ∈ F, S ∉ G → ∃ T ∈ Q, T ⊂ S := by
    intro S hS hSG
    have : ∃ U ∈ F ∪ Q, U ⊂ S := by
      by_contra hcon
      exact hSG ((mem_reduceFam _ _).mpr ⟨Finset.mem_union_left _ hS, hcon⟩)
    obtain ⟨U, hU, hUS⟩ := this
    rcases Finset.mem_union.mp hU with hUF | hUQ
    · exact absurd ⟨U, hUF, hUS⟩ (hredF S hS)
    · exact ⟨U, hUQ, hUS⟩
  have hQG : ∀ T ∈ Q, T ∈ G := by
    intro T hT
    refine (mem_reduceFam _ _).mpr ⟨Finset.mem_union_right _ hT, ?_⟩
    rintro ⟨U, hU, hUT⟩
    rcases Finset.mem_union.mp hU with hUF | hUQ
    · exact hQF U hUF T hT hUT.1
    · have := Finset.card_lt_card hUT
      rw [hQ U hUQ, hQ T hT] at this
      omega
  have hGsub : ∀ S ∈ G, S ∈ F ∪ Q := fun S hS => ((mem_reduceFam _ _).mp hS).1
  obtain ⟨htau, hsp⟩ := tau_spec d j F
  -- the layers of `G` up to `τ(F)` are almost sparse, hence `τ(F) ≤ τ(G)`
  have hspG : ∀ s ∈ Finset.Icc 1 (tau d j F), AlmostSparseLayer d j G s := by
    intro s hs
    by_cases hsh : s = h
    · subst hsh
      apply noFlower_mono _ s _ has
      intro S hS
      obtain ⟨hSG, hSc⟩ := (mem_layer _ _ _).mp hS
      rcases Finset.mem_union.mp (hGsub S hSG) with hSF | hSQ
      · exact Finset.mem_union_left _ ((mem_layer _ _ _).mpr ⟨hSF, hSc⟩)
      · exact Finset.mem_union_right _ hSQ
    · apply noFlower_mono _ s _ (hsp s hs)
      intro S hS
      obtain ⟨hSG, hSc⟩ := (mem_layer _ _ _).mp hS
      rcases Finset.mem_union.mp (hGsub S hSG) with hSF | hSQ
      · exact (mem_layer _ _ _).mpr ⟨hSF, hSc⟩
      · exact absurd (hSc.symm.trans (hQ S hSQ)) hsh
  have htauG : tau d j F ≤ tau d j G :=
    le_tau d j G _ (Finset.mem_Icc.mpr ⟨le_trans hh₁ hh, htau⟩) hspG
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hwh := ws_nonneg d j h hd hj
  set X : ℝ := ws d j h * Q.card with hX
  have hX0 : 0 ≤ X := by positivity
  set Y : ℝ := X / (2 * d) with hY
  have hY0 : 0 ≤ Y := by positivity
  -- per-layer comparison
  have hterm : ∀ s ∈ Finset.Icc 1 (tau d j F),
      ws d j s * (layer F s).card + ((if s = h then X else 0) - (if h < s then Y else 0)) ≤
        ws d j s * (layer G s).card := by
    intro s hs
    have hws := ws_nonneg d j s hd hj
    have hFsub : s ≤ h → layer F s ⊆ layer G s := by
      intro hsh S hS
      obtain ⟨hSF, hSc⟩ := (mem_layer _ _ _).mp hS
      refine (mem_layer _ _ _).mpr ⟨?_, hSc⟩
      by_contra hSG
      obtain ⟨T, hTQ, hTS⟩ := hFG S hSF hSG
      have := Finset.card_lt_card hTS
      rw [hQ T hTQ] at this
      omega
    rcases lt_trichotomy s h with hlt | heq | hgt
    · rw [if_neg (by omega), if_neg (by omega), sub_zero, add_zero]
      have : ((layer F s).card : ℝ) ≤ (layer G s).card := by
        exact_mod_cast Finset.card_le_card (hFsub hlt.le)
      exact mul_le_mul_of_nonneg_left this hws
    · subst heq
      rw [if_pos rfl, if_neg (lt_irrefl _), sub_zero]
      have hdisj : Disjoint (layer F s) Q := by
        rw [Finset.disjoint_left]
        intro S hS hSQ
        exact hQnotF S hSQ ((mem_layer _ _ _).mp hS).1
      have hsub : layer F s ∪ Q ⊆ layer G s := by
        intro S hS
        rcases Finset.mem_union.mp hS with hS | hS
        · exact hFsub le_rfl hS
        · exact (mem_layer _ _ _).mpr ⟨hQG S hS, hQ S hS⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at this
      have : ((layer F s).card : ℝ) + Q.card ≤ (layer G s).card := by exact_mod_cast this
      rw [hX]
      nlinarith
    · rw [if_neg (by omega), if_pos hgt, zero_sub]
      have hcov : layer F s ⊆ layer G s ∪ Q.biUnion fun T => (layer F s).filter fun S => T ⊆ S := by
        intro S hS
        obtain ⟨hSF, hSc⟩ := (mem_layer _ _ _).mp hS
        by_cases hSG : S ∈ G
        · exact Finset.mem_union_left _ ((mem_layer _ _ _).mpr ⟨hSG, hSc⟩)
        · obtain ⟨T, hTQ, hTS⟩ := hFG S hSF hSG
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨T, hTQ, ?_⟩)
          exact Finset.mem_filter.mpr ⟨hS, hTS.1⟩
      have hc1 := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
      have hc2 := (Finset.card_biUnion_le (s := Q)
        (t := fun T => (layer F s).filter fun S => T ⊆ S))
      have hc3 : ∑ T ∈ Q, ((((layer F s).filter fun S => T ⊆ S).card : ℕ) : ℝ) ≤
          Q.card * (2 * tp d j (s - h)) := by
        calc _ ≤ ∑ _T ∈ Q, 2 * tp d j (s - h) := Finset.sum_le_sum fun T hT =>
              star_bound d j hd hj F h s hh₁ hgt (hsp s hs) T (hQ T hT)
          _ = Q.card * (2 * tp d j (s - h)) := by simp
      have hcR : ((layer F s).card : ℝ) ≤ (layer G s).card + Q.card * (2 * tp d j (s - h)) := by
        have : ((layer F s).card : ℝ) ≤ (layer G s).card +
            ∑ T ∈ Q, ((((layer F s).filter fun S => T ⊆ S).card : ℕ) : ℝ) := by
          have := hc1.trans (Nat.add_le_add_left hc2 _)
          exact_mod_cast this
        linarith
      have hprod := ws_mul_tp_sub d j hd hj hgt.le
      have key : ws d j s * (Q.card * (2 * tp d j (s - h))) = Y := by
        rw [hY, hX, show ws d j s * (Q.card * (2 * tp d j (s - h))) =
          2 * Q.card * (ws d j s * tp d j (s - h)) by ring, hprod]
        have hd0 : (d : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      have := mul_le_mul_of_nonneg_left hcR hws
      rw [mul_add, key] at this
      linarith
  -- summing
  have hsumG : ∑ s ∈ Finset.Icc 1 (tau d j F), ws d j s * (layer G s).card ≤
      ∑ s ∈ Finset.Icc 1 (tau d j G), ws d j s * (layer G s).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right htauG)
      (fun s _ _ => mul_nonneg (ws_nonneg d j s hd hj) (Nat.cast_nonneg _))
  have hsum1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum1
  have hmem : h ∈ Finset.Icc 1 (tau d j F) := Finset.mem_Icc.mpr ⟨hh₁, hh⟩
  rw [Finset.sum_ite_eq', if_pos hmem] at hsum1
  have hYsum : ∑ s ∈ Finset.Icc 1 (tau d j F), (if h < s then Y else 0) ≤ (d - 1 : ℝ) * Y := by
    calc _ ≤ ∑ s ∈ Finset.Icc 1 (tau d j F), (Y - if s = 1 then Y else 0) := by
          apply Finset.sum_le_sum
          intro s hs
          by_cases h1 : h < s
          · rw [if_pos h1, if_neg (by omega)]; linarith
          · rw [if_neg h1]
            split_ifs <;> linarith
      _ ≤ ∑ s ∈ Finset.Icc 1 d, (Y - if s = 1 then Y else 0) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right htau)
          intro s _ _
          split_ifs <;> linarith
      _ = (d - 1 : ℝ) * Y := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Finset.sum_ite_eq',
            if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩), nsmul_eq_mul]
          push_cast
          ring
  have hYX : (d - 1 : ℝ) * Y ≤ X / 2 := by
    rw [hY]
    have hd0 : (0 : ℝ) < 2 * d := by linarith
    rw [mul_div_assoc', div_le_div_iff₀ hd0 (by norm_num)]
    nlinarith
  unfold mu
  have : ws d j h / 2 * Q.card = X / 2 := by rw [hX]; ring
  rw [this]
  linarith
