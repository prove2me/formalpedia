-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:49:13.67667+00:00
-- url     : https://prove2.me/submissions/a1980069-2d9d-4d4d-ad6b-ae58b182e563

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Halving

section
set_option autoImplicit false

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.Dev.L41
open RandOnlineSetCoverSqrt.LowerBound

open Classical

section General
variable {m T : ℕ}

theorem sameHistory_refl (t : Fin T) (z : Trajectory m T) : sameHistory t z z :=
  fun _ _ => ⟨rfl, rfl⟩

theorem sameHistory_symm {t : Fin T} {z h : Trajectory m T} (H : sameHistory t z h) :
    sameHistory t h z :=
  fun s hs => ⟨(H s hs).1.symm, (H s hs).2.symm⟩

theorem sameHistory_trans {t : Fin T} {a b c : Trajectory m T} (H1 : sameHistory t a b)
    (H2 : sameHistory t b c) : sameHistory t a c :=
  fun s hs => ⟨(H1 s hs).1.trans (H2 s hs).1, (H1 s hs).2.trans (H2 s hs).2⟩

theorem eventMass_eq (p : PMF (Trajectory m T)) (E : Trajectory m T → Prop) :
    eventMass p E = ∑ z, if E z then p z else 0 := rfl

theorem sum_p (p : PMF (Trajectory m T)) : ∑ z, p z = 1 := by
  have := p.tsum_coe
  rwa [tsum_fintype] at this

theorem single_le_mass (p : PMF (Trajectory m T)) (E : Trajectory m T → Prop)
    (z : Trajectory m T) (hz : E z) : p z ≤ eventMass p E := by
  rw [eventMass_eq]
  have := Finset.single_le_sum (f := fun z => if E z then p z else 0)
    (fun _ _ => zero_le) (Finset.mem_univ z)
  simpa [hz] using this

theorem mass_ne_top (p : PMF (Trajectory m T)) (E : Trajectory m T → Prop) :
    eventMass p E ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  rw [← sum_p p, eventMass_eq]
  apply Finset.sum_le_sum
  intro z _
  split_ifs <;> simp

theorem mass_congr (p : PMF (Trajectory m T)) (t : Fin T) {h h' : Trajectory m T}
    (H : sameHistory t h h') :
    eventMass p (fun z => sameHistory t z h) = eventMass p (fun z => sameHistory t z h') := by
  have : (fun z => sameHistory t z h) = (fun z => sameHistory t z h') := by
    funext z
    apply propext
    exact ⟨fun h1 => sameHistory_trans h1 H, fun h1 => sameHistory_trans h1 (sameHistory_symm H)⟩
  rw [this]

theorem split_by_next (p : PMF (Trajectory m T)) (t : Fin T) (h : Trajectory m T)
    (g : Family m → ℝ≥0∞) :
    ∑ z, (if sameHistory t z h then p z * g (z.1 t.succ) else 0) =
      ∑ D, g D * eventMass p (fun z => sameHistory t z h ∧ z.1 t.succ = D) := by
  simp only [eventMass_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : sameHistory t z h
  · rw [if_pos hz, Finset.sum_eq_single (z.1 t.succ)]
    · simp [hz, mul_comm]
    · intro D _ hD
      simp [hz, Ne.symm hD]
    · simp
  · simp [hz]

theorem sum_halves (c : Family m) (g : Family m → ℝ≥0∞) (x : ℝ≥0∞) :
    ∑ D, g D * (if D ⊆ c ∧ D.card = c.card / 2 then x else 0) =
      (∑ D ∈ c.powersetCard (c.card / 2), g D) * x := by
  rw [Finset.sum_mul]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext D
  simp [Finset.mem_powersetCard]

/-- Average of `g` over the halves of `c`. -/
noncomputable def avg (c : Family m) (g : Family m → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ D ∈ c.powersetCard (c.card / 2), g D) / (Nat.choose c.card (c.card / 2) : ℝ≥0∞)

/-- The halving equation, as a hypothesis. -/
def HalvingEq (p : PMF (Trajectory m T)) : Prop :=
  ∀ (t : Fin T) (h : Trajectory m T) (D : Family m),
    eventMass p (fun z => sameHistory t z h ∧ z.1 t.succ = D) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        eventMass p (fun z => sameHistory t z h) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0

/-- Tower identity: conditioning on the history through `t`, the next family is a uniform half. -/
theorem tower (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (t : Fin T)
    (Φ : Trajectory m T → Family m → ℝ≥0∞) (hΦ : ∀ z z', sameHistory t z z' → Φ z = Φ z') :
    ∑ z, p z * Φ z (z.1 t.succ) = ∑ z, p z * avg (z.1 t.castSucc) (Φ z) := by
  set M : Trajectory m T → ℝ≥0∞ := fun h => eventMass p (fun z => sameHistory t z h) with hM
  have step1 : ∀ z, p z * Φ z (z.1 t.succ) =
      ∑ z', if sameHistory t z z' then p z' / M z' * (p z * Φ z (z.1 t.succ)) else 0 := by
    intro z
    by_cases hz : p z = 0
    · simp [hz]
    have hM0 : M z ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hz)
      (single_le_mass p _ z (sameHistory_refl t z)))
    have hMt : M z ≠ ⊤ := mass_ne_top p _
    have e1 : ∀ z', (if sameHistory t z z' then p z' / M z' * (p z * Φ z (z.1 t.succ)) else 0)
        = (if sameHistory t z' z then p z' else 0) * (M z)⁻¹ * (p z * Φ z (z.1 t.succ)) := by
      intro z'
      by_cases h1 : sameHistory t z z'
      · rw [if_pos h1, if_pos (sameHistory_symm h1)]
        rw [hM]
        simp only
        rw [mass_congr p t (sameHistory_symm h1), div_eq_mul_inv]
      · rw [if_neg h1, if_neg (fun h2 => h1 (sameHistory_symm h2))]
        simp
    rw [Finset.sum_congr rfl (fun z' _ => e1 z'), ← Finset.sum_mul, ← Finset.sum_mul]
    have : (∑ z', if sameHistory t z' z then p z' else 0) = M z := rfl
    rw [this, ENNReal.mul_inv_cancel hM0 hMt, one_mul]
  rw [Finset.sum_congr rfl (fun z _ => step1 z), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z' _
  have e2 : ∀ z, (if sameHistory t z z' then p z' / M z' * (p z * Φ z (z.1 t.succ)) else 0)
      = p z' / M z' * (if sameHistory t z z' then p z * Φ z' (z.1 t.succ) else 0) := by
    intro z
    by_cases h1 : sameHistory t z z'
    · rw [if_pos h1, if_pos h1, hΦ z z' h1]
    · rw [if_neg h1, if_neg h1, mul_zero]
  rw [Finset.sum_congr rfl (fun z _ => e2 z), ← Finset.mul_sum, split_by_next p t z' (Φ z')]
  simp only [hhalf t z' _]
  rw [sum_halves]
  by_cases hz : p z' = 0
  · simp [hz]
  have hM0 : M z' ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hz)
    (single_le_mass p _ z' (sameHistory_refl t z')))
  have hMt : M z' ≠ ⊤ := mass_ne_top p _
  have hMdef : eventMass p (fun z => sameHistory t z z') = M z' := rfl
  rw [hMdef, avg]
  simp only [div_eq_mul_inv]
  calc p z' * (M z')⁻¹ * ((∑ D ∈ (z'.1 t.castSucc).powersetCard ((z'.1 t.castSucc).card / 2), Φ z' D)
        * (M z' * (((z'.1 t.castSucc).card.choose ((z'.1 t.castSucc).card / 2) : ℕ) : ℝ≥0∞)⁻¹))
      = p z' * ((M z')⁻¹ * M z') * ((∑ D ∈ (z'.1 t.castSucc).powersetCard
          ((z'.1 t.castSucc).card / 2), Φ z' D)
        * (((z'.1 t.castSucc).card.choose ((z'.1 t.castSucc).card / 2) : ℕ) : ℝ≥0∞)⁻¹) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hM0 hMt, mul_one]

end General

section Specific
variable {m T : ℕ}

/-- The witness chosen from the current pair. -/
noncomputable def wit (c : Family m) (X : Candidate m) : Candidate m :=
  if h : ∃ W ∈ c, W ⊆ X then h.choose else if h' : c.Nonempty then h'.choose else ∅

theorem wit_mem {c : Family m} {X : Candidate m} (hc : c.Nonempty) : wit c X ∈ c := by
  unfold wit
  split_ifs with h
  · exact h.choose_spec.1
  · exact hc.choose_spec

theorem wit_spec {c : Family m} {X : Candidate m} (h : ∃ W ∈ c, W ⊆ X) :
    wit c X ∈ c ∧ wit c X ⊆ X := by
  unfold wit
  rw [dif_pos h]
  exact h.choose_spec

/-- Witness at step `s`. -/
noncomputable def Wt (z : Trajectory m T) (s : Fin T) : Candidate m :=
  wit (z.1 s.castSucc) (z.2 s.castSucc)

/-- Discarded steps before `t`. -/
noncomputable def disc (z : Trajectory m T) (t : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun s => s.val < t ∧ Wt z s ∉ z.1 s.succ)

/-- The potential `(1/3)^(number of discards before t)`. -/
noncomputable def F (z : Trajectory m T) (t : ℕ) : ℝ≥0∞ := 3⁻¹ ^ (disc z t).card

theorem F_zero (z : Trajectory m T) : F z 0 = 1 := by
  simp [F, disc]

theorem F_succ (z : Trajectory m T) (t : Fin T) :
    F z (t.val + 1) = F z t.val * (if Wt z t ∈ z.1 t.succ then 1 else 3⁻¹) := by
  unfold F
  by_cases hW : Wt z t ∈ z.1 t.succ
  · rw [if_pos hW, mul_one]
    congr 2
    ext s
    simp only [disc, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact h
      · exact absurd (Fin.ext h ▸ hW) h2
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rw [if_neg hW]
    have : disc z (t.val + 1) = insert t (disc z t.val) := by
      ext s
      simp only [disc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl (Fin.ext h)
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨by omega, hW⟩
        · exact ⟨by omega, h2⟩
    rw [this, Finset.card_insert_of_notMem (by simp [disc]), pow_succ]

theorem F_ne_top (z : Trajectory m T) (t : ℕ) : F z t ≠ ⊤ := by
  unfold F
  exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))

theorem disc_congr {t : Fin T} {z z' : Trajectory m T} (H : sameHistory t z z') :
    disc z t.val = disc z' t.val := by
  ext s
  simp only [disc, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have a := H s.castSucc (by simp; omega)
    have b := H s.succ (by simp; omega)
    simp only [Wt] at h2 ⊢
    rw [← a.1, ← a.2, ← b.1]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have a := H s.castSucc (by simp; omega)
    have b := H s.succ (by simp; omega)
    simp only [Wt] at h2 ⊢
    rw [a.1, a.2, b.1]; exact h2

theorem Wt_congr {t : Fin T} {z z' : Trajectory m T} (H : sameHistory t z z') :
    Wt z t = Wt z' t := by
  have a := H t.castSucc (by simp)
  simp only [Wt]; rw [a.1, a.2]

/-- Combinatorial core: averaging the one-step factor over the halves gives `2/3`. -/
theorem avg_factor (c : Family m) (W : Candidate m) (hW : W ∈ c) (a : ℕ) (ha : 1 ≤ a)
    (hc : c.card = 2 * a) :
    avg c (fun D => if W ∈ D then (1 : ℝ≥0∞) else 3⁻¹) = 2 * 3⁻¹ := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hhalf : c.card / 2 = b + 1 := by omega
  have hout : ((c.powersetCard (b + 1)).filter (fun D => ¬ W ∈ D)).card
      = Nat.choose (2 * b + 1) (b + 1) := by
    have : (c.powersetCard (b + 1)).filter (fun D => ¬ W ∈ D) = (c.erase W).powersetCard (b + 1) := by
      ext D
      simp [Finset.mem_powersetCard, Finset.subset_erase, and_right_comm]
    rw [this, Finset.card_powersetCard, Finset.card_erase_of_mem hW, hc]
    congr 1
  have htot : (c.powersetCard (b + 1)).card = 2 * Nat.choose (2 * b + 1) (b + 1) := by
    rw [Finset.card_powersetCard, hc,
      show 2 * (b + 1) = (2 * b + 1) + 1 by ring, Nat.choose_succ_succ, ← Nat.choose_symm_half]
    ring
  have hin : ((c.powersetCard (b + 1)).filter (fun D => W ∈ D)).card
      = Nat.choose (2 * b + 1) (b + 1) := by
    have := Finset.card_filter_add_card_filter_not (s := c.powersetCard (b + 1)) (fun D => W ∈ D)
    omega
  unfold avg
  rw [hhalf, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hin, hout]
  rw [show (c.card.choose (b + 1) : ℝ≥0∞) = ((c.powersetCard (b + 1)).card : ℝ≥0∞) by
    rw [Finset.card_powersetCard], htot]
  set K : ℕ := Nat.choose (2 * b + 1) (b + 1) with hK
  have hKpos : 0 < K := Nat.choose_pos (by omega)
  have h0 : ((2 * K : ℕ) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  have ht : ((2 * K : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [eq_comm, ENNReal.eq_div_iff h0 ht]
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  push_cast
  calc 2 * (K : ℝ≥0∞) * (2 * 3⁻¹) = K * (3 * 3⁻¹ + 3⁻¹) := by ring
    _ = (K : ℝ≥0∞) + K * 3⁻¹ := by rw [h3]; ring

/-- Support facts from the halving equation. -/
theorem support_step (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (z : Trajectory m T)
    (hz : p z ≠ 0) (t : Fin T) :
    z.1 t.succ ⊆ z.1 t.castSucc ∧ (z.1 t.succ).card = (z.1 t.castSucc).card / 2 := by
  have h1 := hhalf t z (z.1 t.succ)
  by_contra hc
  rw [if_neg hc] at h1
  have h2 := single_le_mass p (fun z' => sameHistory t z' z ∧ z'.1 t.succ = z.1 t.succ) z
    ⟨sameHistory_refl t z, rfl⟩
  rw [h1] at h2
  exact hz (le_antisymm h2 zero_le)

theorem support_antitone (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (z : Trajectory m T)
    (hz : p z ≠ 0) : Antitone z.1 := by
  rw [Fin.antitone_iff_succ_le]
  intro t
  exact (support_step p hhalf z hz t).1

theorem support_card (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (C₀ : Family m)
    (hC : C₀.card = 2 ^ T) (z : Trajectory m T) (hz : p z ≠ 0) (h0 : z.1 0 = C₀) :
    ∀ (i : ℕ) (hi : i < T + 1), (z.1 ⟨i, hi⟩).card = 2 ^ (T - i) := by
  intro i
  induction i with
  | zero => intro hi; simpa using (show (z.1 0).card = 2 ^ T by rw [h0, hC])
  | succ i ih =>
    intro hi
    have h := (support_step p hhalf z hz ⟨i, by omega⟩).2
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h
    rw [h, ih (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, T - i = d + 1 := ⟨T - i - 1, by omega⟩
    rw [hd, show T - (i + 1) = d by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- One step of the potential argument. -/
theorem one_step (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (C₀ : Family m)
    (hC : C₀.card = 2 ^ T) (h0 : ∀ z, p z ≠ 0 → z.1 0 = C₀) (t : Fin T) :
    ∑ z, p z * F z (t.val + 1) = 2 * 3⁻¹ * ∑ z, p z * F z t.val := by
  have := tower p hhalf t (fun z D => F z t.val * (if Wt z t ∈ D then 1 else 3⁻¹))
    (fun z z' H => by
      funext D
      simp only [F, disc_congr H, Wt_congr H])
  simp only [← F_succ] at this
  rw [this, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p z = 0
  · simp [hz]
  have hcard := support_card p hhalf C₀ hC z hz (h0 z hz) t.val (by omega)
  have hcs : z.1 t.castSucc = z.1 ⟨t.val, by omega⟩ := rfl
  have hne : (z.1 t.castSucc).Nonempty := by
    rw [← Finset.card_pos, hcs, hcard]; positivity
  have hav : avg (z.1 t.castSucc) (fun D => F z t.val * (if Wt z t ∈ D then 1 else 3⁻¹)) =
      F z t.val * avg (z.1 t.castSucc) (fun D => if Wt z t ∈ D then 1 else 3⁻¹) := by
    simp only [avg, ← Finset.mul_sum, mul_div_assoc]
  rw [hav, avg_factor (z.1 t.castSucc) (Wt z t) (wit_mem hne) (2 ^ (T - t.val - 1))
    Nat.one_le_two_pow (by
      rw [hcs, hcard, ← pow_succ']; congr 1; omega)]
  ring

theorem expect_F (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) (C₀ : Family m)
    (hC : C₀.card = 2 ^ T) (h0 : ∀ z, p z ≠ 0 → z.1 0 = C₀) :
    ∀ n, n ≤ T → ∑ z, p z * F z n = (2 * 3⁻¹) ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [F_zero, sum_p]
  | succ n ih =>
    intro hn
    have := one_step p hhalf C₀ hC h0 ⟨n, by omega⟩
    simp only at this
    rw [this, ih (by omega), pow_succ, mul_comm]

/-- Distinctness: on the bad event, fewer than `q` discards. -/
theorem disc_lt (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) {k q r : ℕ} (C₀ : Family m)
    (hexpand : UnionExpanding k q r C₀)
    (h0 : ∀ z, p z ≠ 0 → z.1 0 = C₀)
    (hmono : ∀ z, p z ≠ 0 → ∀ t : Fin T, z.2 t.castSucc ⊆ z.2 t.succ)
    (hwitness : ∀ z, p z ≠ 0 → ∀ t : Fin T,
      (z.2 t.castSucc).card ≤ r → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc)
    (z : Trajectory m T) (hz : p z ≠ 0) (hX : (z.2 (Fin.last T)).card ≤ r) :
    (disc z T).card < q := by
  have hanti := support_antitone p hhalf z hz
  have hmon : Monotone z.2 := by
    rw [Fin.monotone_iff_le_succ]; exact hmono z hz
  have hW : ∀ s : Fin T, Wt z s ∈ z.1 s.castSucc ∧ Wt z s ⊆ z.2 s.castSucc := by
    intro s
    apply wit_spec
    apply hwitness z hz s
    exact le_trans (Finset.card_le_card (hmon (Fin.le_last _))) hX
  set S := disc z T with hS
  have hmemS : ∀ s, s ∈ S ↔ Wt z s ∉ z.1 s.succ := by
    intro s; simp [hS, disc]
  have hinj : Set.InjOn (Wt z) S := by
    have key : ∀ s1 s2 : Fin T, s1 ∈ S → s1 < s2 → Wt z s1 ≠ Wt z s2 := by
      intro s1 s2 h1 hlt heq
      have hle : s1.succ ≤ s2.castSucc := by
        rw [Fin.le_def]; simp; exact hlt
      apply (hmemS s1).mp h1
      rw [heq]
      exact hanti hle (hW s2).1
    intro s1 h1 s2 h2 heq
    rcases lt_trichotomy s1 s2 with h | h | h
    · exact absurd heq (key s1 s2 h1 h)
    · exact h
    · exact absurd heq.symm (key s2 s1 h2 h)
  by_contra hcon
  push Not at hcon
  set Q := S.image (Wt z) with hQ
  have hQcard : Q.card = S.card := Finset.card_image_of_injOn hinj
  obtain ⟨Q', hQ'sub, hQ'card⟩ := Finset.exists_subset_card_eq (show q ≤ Q.card by omega)
  have hQC : Q ⊆ C₀ := by
    intro W hWQ
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hWQ
    rw [← h0 z hz]
    exact hanti (Fin.zero_le _) (hW s).1
  have hU : Q'.biUnion id ⊆ z.2 (Fin.last T) := by
    intro x hx
    obtain ⟨W, hWQ', hxW⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp (hQ'sub hWQ')
    exact hmon (Fin.le_last _) ((hW s).2 hxW)
  have hlt := hexpand.2.2.2.2.2 Q' (hQ'sub.trans hQC) hQ'card
  have := Finset.card_le_card hU
  omega

theorem one_le_F (p : PMF (Trajectory m T)) (hhalf : HalvingEq p) {k q r : ℕ} (C₀ : Family m)
    (hexpand : UnionExpanding k q r C₀)
    (h0 : ∀ z, p z ≠ 0 → z.1 0 = C₀)
    (hmono : ∀ z, p z ≠ 0 → ∀ t : Fin T, z.2 t.castSucc ⊆ z.2 t.succ)
    (hwitness : ∀ z, p z ≠ 0 → ∀ t : Fin T,
      (z.2 t.castSucc).card ≤ r → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc)
    (z : Trajectory m T) (hz : p z ≠ 0) (hX : (z.2 (Fin.last T)).card ≤ r) :
    1 ≤ (3 : ℝ≥0∞) ^ q * F z T := by
  have hJ := disc_lt p hhalf C₀ hexpand h0 hmono hwitness z hz hX
  unfold F
  set J := (disc z T).card
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [show q = (q - J) + J by omega, pow_add, mul_assoc, ← mul_pow, h3, one_pow, mul_one]
  exact one_le_pow₀ (by norm_num)

theorem exp_bound (q : ℕ) : ((16 : ℝ) / 27) ^ q ≤ Real.exp (-(q : ℝ) / 4) := by
  have h1 : (16 : ℝ) / 27 ≤ Real.exp (-1 / 4) := by
    have := Real.add_one_le_exp (-1 / 4)
    linarith
  rw [show -(q : ℝ) / 4 = q * (-1 / 4) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) h1 q

end Specific

end RandOnlineSetCoverSqrt.Dev.L41

namespace RandOnlineSetCoverSqrt.LowerBound
open RandOnlineSetCoverSqrt.Dev.L41 in
theorem chk_lemma_4_1 {m k q r : ℕ} (C₀ : Family m)
    (hexpand : UnionExpanding k q r C₀) (hsize : C₀.card = 2 ^ (4 * q))
    (p : PMF (Trajectory m (4 * q))) (hprocess : HalvingProcess p C₀)
    (hwitness : ∀ z, p z ≠ 0 → ∀ t : Fin (4 * q),
      (z.2 t.castSucc).card ≤ r → ∃ W ∈ z.1 t.castSucc, W ⊆ z.2 t.castSucc) :
    (1 - Real.exp (-(q : ℝ) / 4)) * (r : ℝ) ≤ terminalExpectation p := by
  classical
  obtain ⟨h0, hmono, hhalf⟩ := hprocess
  have hE := expect_F p hhalf C₀ hsize h0 (4 * q) le_rfl
  have hone := one_le_F p hhalf C₀ hexpand h0 hmono hwitness
  -- real versions
  have hp_ne_top : ∀ z, p z ≠ ⊤ := fun z => PMF.apply_ne_top p z
  have hsum1 : ∑ z, (p z).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun z _ => hp_ne_top z), sum_p]; simp
  have hsumF : ∑ z, (p z).toReal * (F z (4 * q)).toReal = (2 / 3 : ℝ) ^ (4 * q) := by
    have := congrArg ENNReal.toReal hE
    rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top (hp_ne_top z) (F_ne_top z (4 * q)))] at this
    simp only [ENNReal.toReal_mul] at this
    rw [this]
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv, div_eq_mul_inv]
  have hpt : ∀ z, (p z).toReal * (r : ℝ) - (r : ℝ) * 3 ^ q * ((p z).toReal * (F z (4 * q)).toReal)
      ≤ (p z).toReal * ((z.2 (Fin.last (4 * q))).card : ℝ) := by
    intro z
    have ha : 0 ≤ (p z).toReal := ENNReal.toReal_nonneg
    have hf : 0 ≤ (F z (4 * q)).toReal := ENNReal.toReal_nonneg
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    by_cases hX : (z.2 (Fin.last (4 * q))).card ≤ r
    · by_cases hz : p z = 0
      · simp [hz]
      have h1 := hone z hz hX
      have h2 : (1 : ℝ) ≤ 3 ^ q * (F z (4 * q)).toReal := by
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (F_ne_top z (4 * q))) h1
        simpa [ENNReal.toReal_mul, ENNReal.toReal_pow] using this
      have : (p z).toReal * (r : ℝ) ≤ (r : ℝ) * 3 ^ q * ((p z).toReal * (F z (4 * q)).toReal) := by
        nlinarith [mul_nonneg ha hr]
      nlinarith [mul_nonneg ha (Nat.cast_nonneg (α := ℝ) (z.2 (Fin.last (4 * q))).card)]
    · push Not at hX
      have : (r : ℝ) ≤ ((z.2 (Fin.last (4 * q))).card : ℝ) := by exact_mod_cast hX.le
      have h4 : 0 ≤ (r : ℝ) * 3 ^ q * ((p z).toReal * (F z (4 * q)).toReal) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this ha]
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hpt z)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum1, hsumF] at hsum
  unfold terminalExpectation
  have hc : (3 : ℝ) ^ q * (2 / 3 : ℝ) ^ (4 * q) = (16 / 27 : ℝ) ^ q := by
    rw [pow_mul, ← mul_pow]; norm_num
  have heb := exp_bound q
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have : (r : ℝ) * 3 ^ q * (2 / 3 : ℝ) ^ (4 * q) = r * (16 / 27 : ℝ) ^ q := by
    rw [mul_assoc, hc]
  nlinarith [mul_le_mul_of_nonneg_left heb hr]

end RandOnlineSetCoverSqrt.LowerBound
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_4_1 := @RandOnlineSetCoverSqrt.LowerBound.chk_lemma_4_1
