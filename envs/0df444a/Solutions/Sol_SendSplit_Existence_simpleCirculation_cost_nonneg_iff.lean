-- Prove2me | solution 1 for SendSplit.Existence.simpleCirculation_cost_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:33:04.547317+00:00
-- url     : https://prove2.me/submissions/1c62cda4-a339-4e39-af0e-dc86bc9b15ec

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_AugmentedGraph



namespace SendSplit.Existence
variable {n : ℕ}

section RealLemmas
variable {f : ℝ → ℝ}

lemma cc_diff (hf : ConcaveOn ℝ (Set.Ici 0) f) {t : ℝ} (ht : 0 < t) :
    DifferentiableWithinAt ℝ f (Set.Ioi t) t := by
  have h := (hf.neg).differentiableWithinAt_Ioi_of_mem_interior (x := t) (by simpa using ht)
  simpa using h.neg

lemma cc_F2 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    (f s - f t) / (s - t) ≤ derivWithin f (Set.Ioi t) t := by
  have := hf.slope_le_rightDeriv (x := t) (y := s) (Set.mem_Ici.2 ht.le)
    (Set.mem_Ici.2 (ht.le.trans hts.le)) hts (cc_diff hf ht)
  rwa [slope_def_field] at this

lemma cc_F3 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 ≤ t) (hts : t < s) :
    derivWithin f (Set.Ioi s) s ≤ (f s - f t) / (s - t) := by
  have hs : 0 < s := ht.trans_lt hts
  have hd := (cc_diff hf hs).hasDerivWithinAt
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi).mp hd
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : s < y := hy
  rw [slope_def_field]
  exact hf.slope_anti_adjacent (Set.mem_Ici.2 ht) (Set.mem_Ici.2 (hs.le.trans hy'.le)) hts hy'

lemma cc_F4 (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    derivWithin f (Set.Ioi s) s ≤ derivWithin f (Set.Ioi t) t := by
  rcases eq_or_lt_of_le hts with rfl | h
  · exact le_rfl
  · exact (cc_F3 hf ht.le h).trans (cc_F2 hf ht h)

/-- tangent line bound -/
lemma cc_tangent (hf : ConcaveOn ℝ (Set.Ici 0) f) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    f s ≤ f t + derivWithin f (Set.Ioi t) t * (s - t) := by
  have := cc_F2 hf ht hts
  rw [div_le_iff₀ (by linarith)] at this
  linarith

/-- chord bound: f(s)/s ≥ f(T)/T ≥ d(T) -/
lemma cc_lower (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {s T : ℝ} (hs : 0 < s) (hsT : s < T) :
    derivWithin f (Set.Ioi T) T * s ≤ f s := by
  have h1 := cc_F3 hf (le_refl 0) (hs.trans hsT)
  have h2 := hf.slope_anti_adjacent (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 (hs.trans hsT).le) hs hsT
  simp only [h0, sub_zero] at h1 h2
  have hT : 0 < T := hs.trans hsT
  -- d T ≤ f T / T ≤ f s / s
  have h3 : derivWithin f (Set.Ioi T) T ≤ f s / s := by
    have : f T / T ≤ f s / s := by
      have hh : (f T - f s) / (T - s) ≤ f s / s := h2
      rw [div_le_div_iff₀ (by linarith) hs] at hh
      rw [div_le_div_iff₀ hT hs]
      nlinarith
    exact h1.trans this
  rwa [le_div_iff₀ hs] at h3

lemma ereal_coe_sum {ι : Type*} (C : Finset ι) (a : ι → ℝ) :
    ((∑ i ∈ C, a i : ℝ) : EReal) = ∑ i ∈ C, (a i : EReal) := by
  classical
  induction C using Finset.induction_on with
  | empty => simp
  | insert j C hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

theorem sum_slope_iff {ι : Type*} (C : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ C, ConcaveOn ℝ (Set.Ici 0) (g i) ∧ g i 0 = 0) :
    (∀ s : ℝ, 0 ≤ s → 0 ≤ ∑ i ∈ C, g i s) ↔ 0 ≤ ∑ i ∈ C, slopeAtInfty (g i) := by
  classical
  have hE1 : ∀ i ∈ C, ∀ t : ℝ, 0 < t → slopeAtInfty (g i) ≤ ((derivWithin (g i) (Set.Ioi t) t : ℝ) : EReal) := by
    intro i _ t ht
    exact (iInf₂_le t ht)
  constructor
  · intro H
    -- step 1
    have step1 : ∀ t : ℝ, 0 < t → 0 ≤ ∑ i ∈ C, derivWithin (g i) (Set.Ioi t) t := by
      intro t ht
      by_contra hD
      push_neg at hD
      set D := ∑ i ∈ C, derivWithin (g i) (Set.Ioi t) t with hDdef
      set K := ∑ i ∈ C, g i t with hK
      have hDneg : 0 < -D := by linarith
      set s := t + (|K| + 1) / (-D) with hs
      have hst : t < s := by
        have : 0 < (|K| + 1) / (-D) := div_pos (by positivity) hDneg
        linarith
      have hle : ∑ i ∈ C, g i s ≤ K + D * (s - t) := by
        rw [hDdef, Finset.sum_mul, hK, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i hi => ?_
        have := cc_tangent (hg i hi).1 ht hst
        linarith
      have hDs : D * (s - t) = -(|K| + 1) := by
        have hD0 : D ≠ 0 := hD.ne
        rw [hs]; field_simp; ring
      have := H s (by linarith)
      have := le_abs_self K
      linarith
    by_cases hbot : ∃ p ∈ C, slopeAtInfty (g p) = ⊥
    · exfalso
      obtain ⟨p, hp, hpb⟩ := hbot
      set M := ∑ q ∈ C.erase p, derivWithin (g q) (Set.Ioi 1) 1 with hM
      have : ∃ t0 : ℝ, 0 < t0 ∧ derivWithin (g p) (Set.Ioi t0) t0 < -M := by
        by_contra h
        push_neg at h
        have : ((-M : ℝ) : EReal) ≤ slopeAtInfty (g p) :=
          le_iInf₂ fun t ht => EReal.coe_le_coe_iff.2 (h t ht)
        rw [hpb] at this
        exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
      obtain ⟨t0, ht0, hlt⟩ := this
      set t := max t0 1 with htdef
      have htpos : 0 < t := lt_max_of_lt_right one_pos
      have h1 : derivWithin (g p) (Set.Ioi t) t ≤ derivWithin (g p) (Set.Ioi t0) t0 :=
        cc_F4 (hg p hp).1 ht0 (le_max_left _ _)
      have h2 : ∑ q ∈ C.erase p, derivWithin (g q) (Set.Ioi t) t ≤ M :=
        Finset.sum_le_sum fun q hq => cc_F4 (hg q (Finset.mem_of_mem_erase hq)).1 one_pos (le_max_right _ _)
      have := step1 t htpos
      rw [← Finset.add_sum_erase _ _ hp] at this
      linarith
    · push_neg at hbot
      have hr : ∀ i ∈ C, slopeAtInfty (g i) = (((slopeAtInfty (g i)).toReal : ℝ) : EReal) := by
        intro i hi
        refine (EReal.coe_toReal ?_ (hbot i hi)).symm
        exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hE1 i hi 1 one_pos)
      set r : ι → ℝ := fun i => (slopeAtInfty (g i)).toReal with hrdef
      have hsum : ∑ i ∈ C, slopeAtInfty (g i) = ((∑ i ∈ C, r i : ℝ) : EReal) := by
        rw [ereal_coe_sum]
        exact Finset.sum_congr rfl hr
      rw [hsum, EReal.coe_nonneg]
      by_contra hneg
      push_neg at hneg
      set ε : ℝ := -(∑ i ∈ C, r i) / (C.card + 1) with hε
      have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
      have hex : ∀ i ∈ C, ∃ t : ℝ, 0 < t ∧ derivWithin (g i) (Set.Ioi t) t < r i + ε := by
        intro i hi
        by_contra h
        push_neg at h
        have : (((r i + ε : ℝ)) : EReal) ≤ slopeAtInfty (g i) :=
          le_iInf₂ fun t ht => EReal.coe_le_coe_iff.2 (h t ht)
        rw [hr i hi] at this
        have := EReal.coe_le_coe_iff.1 this
        linarith
      choose! t ht using hex
      set T : ℝ := 1 + ∑ i ∈ C, t i with hT
      have hTpos : 0 < T := by
        have : 0 ≤ ∑ i ∈ C, t i := Finset.sum_nonneg fun i hi => (ht i hi).1.le
        linarith
      have hle : ∀ i ∈ C, t i ≤ T := by
        intro i hi
        have := Finset.single_le_sum (f := t) (fun i hi => (ht i hi).1.le) hi
        linarith
      have h1 : ∑ i ∈ C, derivWithin (g i) (Set.Ioi T) T ≤ ∑ i ∈ C, (r i + ε) :=
        Finset.sum_le_sum fun i hi =>
          ((cc_F4 (hg i hi).1 (ht i hi).1 (hle i hi)).trans (ht i hi).2.le)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
      have h2 := step1 T hTpos
      have h3 : (C.card : ℝ) * ε < -(∑ i ∈ C, r i) := by
        rw [hε]
        have hc : (0:ℝ) < C.card + 1 := by positivity
        rw [mul_div_assoc', div_lt_iff₀ hc]
        nlinarith
      linarith
  · intro H s hs
    rcases eq_or_lt_of_le hs with rfl | hs
    · exact le_of_eq (Finset.sum_eq_zero fun i hi => (hg i hi).2).symm
    · have hle : ∑ i ∈ C, slopeAtInfty (g i) ≤ ((∑ i ∈ C, derivWithin (g i) (Set.Ioi (s+1)) (s+1) : ℝ) : EReal) := by
        rw [ereal_coe_sum]
        exact Finset.sum_le_sum fun i hi => hE1 i hi (s+1) (by linarith)
      have h0 : 0 ≤ ∑ i ∈ C, derivWithin (g i) (Set.Ioi (s+1)) (s+1) :=
        EReal.coe_nonneg.1 (H.trans hle)
      calc (0:ℝ) ≤ (∑ i ∈ C, derivWithin (g i) (Set.Ioi (s+1)) (s+1)) * s := mul_nonneg h0 hs.le
        _ = ∑ i ∈ C, derivWithin (g i) (Set.Ioi (s+1)) (s+1) * s := Finset.sum_mul _ _ _
        _ ≤ ∑ i ∈ C, g i s := Finset.sum_le_sum fun i hi =>
            cc_lower (hg i hi).1 (hg i hi).2 hs (by linarith)

end RealLemmas

lemma simple_circ_const (G : ArcGraph n) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ p ∈ support G y, y p.1 p.2 = t0 := by
  classical
  obtain ⟨⟨⟨hnn, hzero⟩, hcons⟩, m, v, hinj, harc, hC⟩ := hy
  have hmemC : ∀ p, p ∈ support G y ↔ ∃ k, p = (v k, v (k + 1)) := by
    intro p
    rw [hC]; simp [eq_comm]
  have hsupp : ∀ i j, y i j ≠ 0 → ∃ k, (i, j) = (v k, v (k + 1)) := by
    intro i j h
    have hA : (i, j) ∈ G.A := by
      by_contra hh; exact h (hzero i j hh)
    exact (hmemC (i, j)).1 (by simp [support, hA, h])
  have hpos : ∀ k, 0 < y (v k) (v (k + 1)) := by
    intro k
    have : (v k, v (k + 1)) ∈ support G y := (hmemC _).2 ⟨k, rfl⟩
    simp only [support, Finset.mem_filter] at this
    exact lt_of_le_of_ne (hnn _ _) (Ne.symm this.2)
  have hstep : ∀ k : Fin (m + 2), y (v k) (v (k + 1)) = y (v (k + 1)) (v (k + 1 + 1)) := by
    intro k
    have h1 := hcons (v (k + 1))
    simp only at h1
    have hin : ∑ j ∈ Finset.univ.filter (fun j => (j, v (k + 1)) ∈ G.A), y j (v (k + 1))
        = y (v k) (v (k + 1)) := by
      rw [Finset.sum_eq_single (v k)]
      · intro j _ hj
        by_contra hne
        obtain ⟨k', hk'⟩ := hsupp j _ hne
        have e1 := (Prod.mk.inj hk').1
        have e2 := hinj (Prod.mk.inj hk').2
        have : k' = k := Eq.symm (by simpa using e2)
        subst this
        exact hj e1
      · intro h; exact absurd (by simpa using harc k) h
    have hout : ∑ k' ∈ Finset.univ.filter (fun k' => (v (k + 1), k') ∈ G.A), y (v (k + 1)) k'
        = y (v (k + 1)) (v (k + 1 + 1)) := by
      rw [Finset.sum_eq_single (v (k + 1 + 1))]
      · intro j _ hj
        by_contra hne
        obtain ⟨k', hk'⟩ := hsupp _ j hne
        have e1 := hinj (Prod.mk.inj hk').1
        have e2 := (Prod.mk.inj hk').2
        have : k' = k + 1 := e1.symm
        subst this
        exact hj e2
      · intro h; exact absurd (by simpa using harc (k + 1)) h
    rw [hin, hout] at h1
    simpa using (sub_eq_zero.1 h1)
  have hconst : ∀ k : Fin (m + 2), y (v k) (v (k + 1)) = y (v 0) (v (0 + 1)) := by
    intro k
    induction k using Fin.induction with
    | zero => rfl
    | succ i ih =>
      rw [← Fin.coeSucc_eq_succ, ← ih]
      exact (hstep _).symm
  refine ⟨y (v 0) (v (0 + 1)), hpos 0, ?_⟩
  intro p hp
  obtain ⟨k, rfl⟩ := (hmemC p).1 hp
  exact hconst k

theorem flowCost_ray (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (y : Fin n → Fin n → ℝ) (t0 : ℝ) (ht : ∀ p ∈ support G y, y p.1 p.2 = t0) (θ : ℝ) :
    flowCost G c (fun i j => θ * y i j) = ∑ p ∈ support G y, c p.1 p.2 (θ * t0) := by
  classical
  unfold flowCost support
  rw [← Finset.sum_filter_add_sum_filter_not G.A (fun p => y p.1 p.2 ≠ 0)]
  have h2 : ∑ p ∈ G.A.filter (fun p => ¬ y p.1 p.2 ≠ 0), c p.1 p.2 (θ * y p.1 p.2) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have : y p.1 p.2 = 0 := not_not.1 hp.2
    rw [this, mul_zero]; exact (hc p hp.1).2
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have := ht p (by simpa [support] using hp)
  show c p.1 p.2 (θ * y p.1 p.2) = _
  rw [this]

theorem simpleCirc_core (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y) :
    (∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j)) ↔
      0 ≤ ∑ p ∈ support G y, slopeAtInfty (c p.1 p.2) := by
  classical
  obtain ⟨t0, ht0, ht⟩ := simple_circ_const G y hy
  rw [← sum_slope_iff (support G y) (fun p => c p.1 p.2)
    (fun p hp => hc p (by simpa [support] using (Finset.mem_filter.1 hp).1))]
  constructor
  · intro H s hs
    have := H (s / t0) (div_nonneg hs ht0.le)
    rw [flowCost_ray G c hc y t0 ht, div_mul_cancel₀ _ ht0.ne'] at this
    exact this
  · intro H θ hθ
    rw [flowCost_ray G c hc y t0 ht]
    exact H _ (mul_nonneg hθ ht0.le)

end SendSplit.Existence

open SendSplit.Existence


theorem solution {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y) :
    (∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j)) ↔
      0 ≤ ∑ p ∈ support G y, slopeAtInfty (c p.1 p.2) := by
  exact simpleCirc_core G c hc y hy
