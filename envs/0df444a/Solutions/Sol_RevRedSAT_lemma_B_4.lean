-- Prove2me | solution 1 for RevRedSAT.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:59:09.401646+00:00
-- url     : https://prove2.me/submissions/59fdd418-e2dd-4e2c-9447-b780383c1fd2

import Mathlib
import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_RevRedSAT_mu

set_option autoImplicit false

namespace RevRedSATB4Aux

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

/-- In an almost sparse layer `F_s` with `s ≥ 2`, at most `2 t_{s-1}` sets contain a given element. -/
lemma elem_bound {n : ℕ} (d j : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (F : Finset (Finset (Fin n)))
    (s : ℕ) (hs : 2 ≤ s) (hA : AlmostSparseLayer d j F s) (u : Fin n) :
    ((((layer F s).filter fun S => u ∈ S).card : ℕ) : ℝ) ≤ 2 * tp d j (s - 1) := by
  classical
  set Gs := (layer F s).filter fun S => u ∈ S with hGs
  have memGs : ∀ S ∈ Gs, S ∈ F ∧ u ∈ S ∧ S.card = s := by
    intro S hS
    rw [hGs, Finset.mem_filter] at hS
    have h1 := hS.1
    simp only [layer, Finset.mem_filter] at h1
    exact ⟨h1.1, hS.2, h1.2⟩
  have ht1 := one_le_tp d j hd hj (show 1 ≤ s - 1 by omega)
  by_cases hc : Gs.card ≤ 1
  · have : ((Gs.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
    linarith
  · push Not at hc
    obtain ⟨S, hS, T, hT, hST⟩ := Finset.one_lt_card.mp hc
    obtain ⟨_, _, hcS⟩ := memGs S hS
    obtain ⟨_, _, hcT⟩ := memGs T hT
    have hcoreS : core Gs ⊆ S := by
      unfold core; exact Finset.inf_le (f := id) hS
    have hcoreT : core Gs ⊆ T := by
      unfold core; exact Finset.inf_le (f := id) hT
    have hucore : u ∈ core Gs := by
      unfold core
      rw [Finset.mem_inf]
      intro V hV
      exact (memGs V hV).2.1
    have hcard_lt : (core Gs).card < s := by
      have hsub : core Gs ⊆ S ∩ T := Finset.subset_inter hcoreS hcoreT
      have hlt : (S ∩ T).card < S.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.inter_subset_left, fun h => hST ?_⟩
        have hST' : S ⊆ T := fun x hx => (Finset.mem_inter.mp (h hx)).2
        exact Finset.eq_of_subset_of_card_le hST' (by omega)
      have := Finset.card_le_card hsub
      omega
    have hflower : IsFlower (layer F s) s Gs := by
      refine ⟨?_, ⟨S, hS⟩, ⟨u, hucore⟩, hcard_lt⟩
      intro V hV
      obtain ⟨hVF, _, hVc⟩ := memGs V hV
      simp only [layer, Finset.mem_filter]
      exact ⟨⟨hVF, hVc⟩, hVc⟩
    have hlt := hA Gs hflower
    have hmono : tp d j (s - (core Gs).card) ≤ tp d j (s - 1) := by
      apply tp_mono d j hd hj
      have : 1 ≤ (core Gs).card := Finset.card_pos.mpr ⟨u, hucore⟩
      omega
    linarith

/-- At most one set of size `1` contains a given element. -/
lemma elem_bound_one {n : ℕ} (F : Finset (Finset (Fin n))) (u : Fin n) :
    ((layer F 1).filter fun S => u ∈ S).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro S hS T hT
  simp only [layer, Finset.mem_filter] at hS hT
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hS.1.2
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hT.1.2
  rw [Finset.mem_singleton] at hS hT
  rw [← hS.2, ← hT.2]

/-- A hitting set `X` covers every layer: `|F_s| ≤ Σ_{x ∈ X} |{S ∈ F_s : x ∈ S}|`. -/
lemma layer_card_le {n : ℕ} (F : Finset (Finset (Fin n))) (X : Finset (Fin n))
    (hX : AlgebraicFPT.HittingSet.IsHitting F X) (s : ℕ) :
    (layer F s).card ≤ ∑ x ∈ X, ((layer F s).filter fun S => x ∈ S).card := by
  classical
  have hsub : layer F s ⊆ X.biUnion fun x => (layer F s).filter fun S => x ∈ S := by
    intro S hS
    have hSF : S ∈ F := (Finset.mem_filter.mp hS).1
    obtain ⟨x, hx⟩ := hX S hSF
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_biUnion]
    exact ⟨x, hx.1, Finset.mem_filter.mpr ⟨hS, hx.2⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

end RevRedSATB4Aux

open RevRedSAT RevRedSATB4Aux in
theorem solution (d j n k : ℕ) (hd : 2 ≤ d) (hj : 2 ≤ j) (hk : 0 < k)
    (F : Finset (Finset (Fin n))) (_hrank : ∀ S ∈ F, S.card ≤ d) (_hne : ∀ S ∈ F, S.Nonempty)
    (_hred : IsReduced F)
    (hX : ∃ X : Finset (Fin n), AlgebraicFPT.HittingSet.IsHitting F X ∧ X.card ≤ k) :
    (k : ℝ) / 4 < mu d j k F := by
  obtain ⟨X, hXhit, hXk⟩ := hX
  obtain ⟨htau, hsparse⟩ := tau_spec d j F
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hXkR : (X.card : ℝ) ≤ k := by exact_mod_cast hXk
  set bnd : ℕ → ℝ := fun s => (k : ℝ) / (4 * d) + if s = 1 then (k : ℝ) / 2 - k / (4 * d) else 0
    with hbnd
  have hbnd_nonneg : ∀ s, 0 ≤ bnd s := by
    intro s
    simp only [hbnd]
    have h1 : (k : ℝ) / (4 * d) ≤ k / 2 := by
      apply div_le_div_of_nonneg_left hkR.le (by norm_num) (by linarith)
    split_ifs <;> [linarith; positivity]
  have hterm : ∀ s ∈ Finset.Icc 1 (tau d j F), ws d j s * (layer F s).card ≤ bnd s := by
    intro s hs
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hAS := hsparse s hs
    have hcov : ((layer F s).card : ℝ) ≤
        ∑ x ∈ X, ((((layer F s).filter fun S => x ∈ S).card : ℕ) : ℝ) := by
      exact_mod_cast layer_card_le F X hXhit s
    have hw := ws_nonneg d j s hd hj
    by_cases hs1' : s = 1
    · subst hs1'
      have hsum : ∑ x ∈ X, ((((layer F 1).filter fun S => x ∈ S).card : ℕ) : ℝ) ≤ X.card := by
        calc _ ≤ ∑ _x ∈ X, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
              exact_mod_cast elem_bound_one F x
          _ = X.card := by simp
      have hw1 : ws d j 1 = 1 / 2 := by
        have := ws_mul_tp d j hd hj (le_refl 1)
        have ht0 : tp d j (1 - 1) = 1 / (4 * d) := by
          unfold tp; simp
        rw [ht0] at this
        have hd0 : (d : ℝ) ≠ 0 := by linarith
        field_simp at this
        linarith
      simp only [hbnd, if_true]
      rw [hw1]
      nlinarith
    · have hs2 : 2 ≤ s := by omega
      have hsum : ∑ x ∈ X, ((((layer F s).filter fun S => x ∈ S).card : ℕ) : ℝ) ≤
          X.card * (2 * tp d j (s - 1)) := by
        calc _ ≤ ∑ _x ∈ X, 2 * tp d j (s - 1) :=
              Finset.sum_le_sum fun x _ => elem_bound d j hd hj F s hs2 hAS x
          _ = X.card * (2 * tp d j (s - 1)) := by simp
      have hwt := ws_mul_tp d j hd hj hs1
      have htp := one_le_tp d j hd hj (show 1 ≤ s - 1 by omega)
      simp only [hbnd, hs1', if_false, add_zero]
      have e : ws d j s * (X.card * (2 * tp d j (s - 1))) = X.card * (2 / (8 * d)) := by
        rw [show ws d j s * (X.card * (2 * tp d j (s - 1))) =
          X.card * 2 * (ws d j s * tp d j (s - 1)) by ring, hwt]
        ring
      have h1 : ws d j s * (layer F s).card ≤ ws d j s * (X.card * (2 * tp d j (s - 1))) :=
        mul_le_mul_of_nonneg_left (hcov.trans hsum) hw
      have h2 : (X.card : ℝ) * (2 / (8 * d)) ≤ k / (4 * d) := by
        rw [show (k : ℝ) / (4 * d) = k * (2 / (8 * d)) by field_simp; ring]
        exact mul_le_mul_of_nonneg_right hXkR (by positivity)
      linarith
  have hsum1 : ∑ s ∈ Finset.Icc 1 (tau d j F), ws d j s * (layer F s).card ≤
      ∑ s ∈ Finset.Icc 1 d, bnd s := by
    calc _ ≤ ∑ s ∈ Finset.Icc 1 (tau d j F), bnd s := Finset.sum_le_sum hterm
      _ ≤ ∑ s ∈ Finset.Icc 1 d, bnd s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right htau)
            (fun s _ _ => hbnd_nonneg s)
  have hsum2 : ∑ s ∈ Finset.Icc 1 d, bnd s = d * ((k : ℝ) / (4 * d)) + (k / 2 - k / (4 * d)) := by
    simp only [hbnd]
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩), nsmul_eq_mul]
    congr 2
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hval : (d : ℝ) * ((k : ℝ) / (4 * d)) = k / 4 := by field_simp
  have hpos : (0 : ℝ) < k / (4 * d) := by positivity
  unfold mu
  linarith
