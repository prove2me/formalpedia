-- Prove2me | solution 1 for PochetWolsey.Capacities.discrete_hull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:08:49.393991+00:00
-- url     : https://prove2.me/submissions/a06ceb39-7cbf-48a7-9136-13905f5ab4af

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

namespace S226P_fdae2afc

open Filter Topology

def Lset {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u}

def Rset {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ u, 0 ≤ y u ∧ y u ≤ 1) ∧
      ∀ t, (⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) ≤ (∑ u ∈ Finset.Iic t, y u)}

lemma int_sum {n : ℕ} (y : Fin n → ℝ) (s : Finset (Fin n)) :
    (∀ u ∈ s, y u = 0 ∨ y u = 1) → ∃ z : ℤ, ∑ u ∈ s, y u = z := by
  induction s using Finset.induction_on with
  | empty => intro _; exact ⟨0, by simp⟩
  | insert a s ha ih =>
    intro hb
    obtain ⟨z, hz⟩ := ih (fun u hu => hb u (Finset.mem_insert_of_mem hu))
    rcases hb a (Finset.mem_insert_self a s) with h | h
    · exact ⟨z, by rw [Finset.sum_insert ha, h, hz]; simp⟩
    · exact ⟨z + 1, by rw [Finset.sum_insert ha, h, hz]; push_cast; ring⟩

lemma L_sub_R {n : ℕ} (C : ℝ) (hC : 0 < C) (d : Fin n → ℝ) : Lset C d ⊆ Rset C d := by
  intro y ⟨hb, hD⟩
  refine ⟨fun u => ?_, fun t => ?_⟩
  · rcases hb u with h | h <;> rw [h] <;> norm_num
  · obtain ⟨z, hz⟩ := int_sum y (Finset.Iic t) (fun u _ => hb u)
    rw [hz]
    have : (∑ u ∈ Finset.Iic t, d u) / C ≤ z := by
      rw [div_le_iff₀ hC]; have := hD t; rw [hz] at this; linarith
    exact_mod_cast Int.ceil_le.2 this

lemma R_convex {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : Convex ℝ (Rset C d) := by
  intro y hy y' hy' a b ha hb hab
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h1', h2'⟩ := hy'
  refine ⟨fun u => ⟨?_, ?_⟩, fun t => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(h1 u).1, (h1' u).1]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [(h1 u).2, (h1' u).2]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have hk1 := h2 t
    have hk2 := h2' t
    generalize ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) = k at hk1 hk2 ⊢
    have hkk : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.2 hk1), mul_nonneg hb (sub_nonneg.2 hk2)]

lemma R_compact {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : IsCompact (Rset C d) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset
  · have : Rset C d = (⋂ u, {y : Fin n → ℝ | 0 ≤ y u} ∩ {y | y u ≤ 1}) ∩
        ⋂ t, {y : Fin n → ℝ | ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) ≤
          ∑ u ∈ Finset.Iic t, y u} := by
      ext y; simp [Rset, forall_and]
    rw [this]
    exact IsClosed.inter (isClosed_iInter fun u =>
      (isClosed_le continuous_const (continuous_apply u)).inter
        (isClosed_le (continuous_apply u) continuous_const))
      (isClosed_iInter fun t => isClosed_le continuous_const
        (continuous_finset_sum _ fun u _ => continuous_apply u))
  · intro y hy
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_true_left]
    exact fun u => hy.1 u

lemma L_finite {n : ℕ} (C : ℝ) (d : Fin n → ℝ) : (Lset C d).Finite := by
  apply (Set.Finite.pi (t := fun _ : Fin n => ({0, 1} : Set ℝ))
    (fun _ => Set.toFinite _)).subset
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_true_left]
  exact hy.1

lemma ext_sub_L {n : ℕ} (C : ℝ) (hC : 0 < C) (d : Fin n → ℝ) :
    (Rset C d).extremePoints ℝ ⊆ Lset C d := by
  classical
  intro y hy
  have hyR := hy.1
  obtain ⟨hbox, hk⟩ := hyR
  -- y binary
  have hbin : ∀ u, y u = 0 ∨ y u = 1 := by
    by_contra hcon
    push_neg at hcon
    let F : Finset (Fin n) := Finset.univ.filter (fun u => y u ≠ 0 ∧ y u ≠ 1)
    have hFne : F.Nonempty := by
      obtain ⟨u, hu⟩ := hcon; exact ⟨u, by simp [F, hu]⟩
    let u1 := F.min' hFne
    have hu1F : u1 ∈ F := F.min'_mem hFne
    have hu1 : y u1 ≠ 0 ∧ y u1 ≠ 1 := by simpa [F] using hu1F
    have hu1min : ∀ u ∈ F, u1 ≤ u := fun u hu => F.min'_le u hu
    have hfr : ∀ u, (y u ≠ 0 ∧ y u ≠ 1) → 0 < y u ∧ y u < 1 := fun u hu =>
      ⟨lt_of_le_of_ne (hbox u).1 (Ne.symm hu.1), lt_of_le_of_ne (hbox u).2 hu.2⟩
    -- strictness lemma
    have hstrict : ∀ t, u1 ≤ t → (∀ u ≤ t, u ≠ u1 → u ∉ F) →
        ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) < ∑ u ∈ Finset.Iic t, y u := by
      intro t ht hnot
      have hsum : ∑ u ∈ Finset.Iic t, y u =
          y u1 + ∑ u ∈ (Finset.Iic t).erase u1, y u := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_Iic.2 ht)]
      obtain ⟨z, hz⟩ := int_sum y ((Finset.Iic t).erase u1) (fun u hu => by
        have hu' := Finset.mem_erase.1 hu
        have := hnot u (Finset.mem_Iic.1 hu'.2) hu'.1
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or,
          not_not] at this
        tauto)
      refine lt_of_le_of_ne (hk t) ?_
      intro heq
      rw [hsum, hz] at heq
      have h01 := hfr u1 hu1
      have : y u1 = ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ - z : ℤ) : ℝ) := by
        push_cast; linarith
      obtain ⟨w, hw⟩ : ∃ w : ℤ, y u1 = w := ⟨_, this⟩
      rw [hw] at h01
      have a1 : (0:ℤ) < w := by exact_mod_cast h01.1
      have a2 : w < 1 := by exact_mod_cast h01.2
      omega
    -- perturbation lemma
    have key : ∀ E : Fin n → ℝ, (∀ u, E u ≠ 0 → 0 < y u ∧ y u < 1) →
        (∀ t, ∑ u ∈ Finset.Iic t, E u ≠ 0 →
          ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) < ∑ u ∈ Finset.Iic t, y u) →
        ∀ᶠ ε in 𝓝 (0:ℝ), y + ε • E ∈ Rset C d := by
      intro E hE hEt
      have hexp : ∀ t (ε : ℝ), ∑ u ∈ Finset.Iic t, (y + ε • E) u =
          ∑ u ∈ Finset.Iic t, y u + ε * ∑ u ∈ Finset.Iic t, E u := by
        intro t ε
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          Finset.mul_sum]
      simp only [Rset, Set.mem_setOf_eq]
      refine (Filter.eventually_all.2 fun u => ?_).and (Filter.eventually_all.2 fun t => ?_)
      · by_cases hu : E u = 0
        · exact Filter.Eventually.of_forall fun ε => by simp [hu, hbox u]
        · have hc : ContinuousAt (fun ε : ℝ => y u + ε * E u) 0 := by fun_prop
          have e1 := continuousAt_const.eventually_lt hc (by simpa using (hE u hu).1)
          have e2 := hc.eventually_lt continuousAt_const (by simpa using (hE u hu).2)
          exact (e1.and e2).mono fun ε hε => by
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            exact ⟨hε.1.le, hε.2.le⟩
      · by_cases ht : ∑ u ∈ Finset.Iic t, E u = 0
        · exact Filter.Eventually.of_forall fun ε => by rw [hexp, ht]; simpa using hk t
        · have hc : ContinuousAt (fun ε : ℝ => ∑ u ∈ Finset.Iic t, y u +
              ε * ∑ u ∈ Finset.Iic t, E u) 0 := by fun_prop
          have := continuousAt_const.eventually_lt hc (by simpa using hEt t ht)
          exact this.mono fun ε hε => by rw [hexp]; exact hε.le
    -- choose direction
    have hdir : ∃ E : Fin n → ℝ, E ≠ 0 ∧ (∀ u, E u ≠ 0 → 0 < y u ∧ y u < 1) ∧
        (∀ t, ∑ u ∈ Finset.Iic t, E u ≠ 0 →
          ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) < ∑ u ∈ Finset.Iic t, y u) := by
      let G : Finset (Fin n) := F.filter (fun u => u1 < u)
      by_cases hG : G.Nonempty
      · let u2 := G.min' hG
        have hu2G : u2 ∈ G := G.min'_mem hG
        have hu2F : u2 ∈ F := (Finset.mem_filter.1 hu2G).1
        have hu12 : u1 < u2 := (Finset.mem_filter.1 hu2G).2
        have hu2 : y u2 ≠ 0 ∧ y u2 ≠ 1 := by simpa [F] using hu2F
        have hu2min : ∀ u ∈ G, u2 ≤ u := fun u hu => G.min'_le u hu
        refine ⟨Pi.single u1 1 - Pi.single u2 1, ?_, ?_, ?_⟩
        · intro h0
          have := congrFun h0 u1
          simp [Pi.single_apply, hu12.ne] at this
        · intro u hu
          by_cases h1 : u = u1
          · rw [h1]; exact hfr u1 hu1
          · by_cases h2 : u = u2
            · rw [h2]; exact hfr u2 hu2
            · simp [Pi.single_apply, h1, h2] at hu
        · intro t ht
          simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single',
            Finset.mem_Iic] at ht
          have ht1 : u1 ≤ t := by
            by_contra h
            have h' : ¬ u2 ≤ t := fun h' => h (le_trans hu12.le h')
            simp [h, h'] at ht
          have ht2 : ¬ u2 ≤ t := by intro h; simp [ht1, h] at ht
          apply hstrict t ht1
          intro u hut hne huF
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact absurd (hu1min u huF) (not_le.2 hlt)
          · have : u ∈ G := Finset.mem_filter.2 ⟨huF, hgt⟩
            exact ht2 (le_trans (hu2min u this) hut)
      · refine ⟨Pi.single u1 1, ?_, ?_, ?_⟩
        · intro h0
          have := congrFun h0 u1
          simp at this
        · intro u hu
          by_cases h1 : u = u1
          · rw [h1]; exact hfr u1 hu1
          · simp [Pi.single_apply, h1] at hu
        · intro t ht
          simp only [Finset.sum_pi_single', Finset.mem_Iic] at ht
          have ht1 : u1 ≤ t := by by_contra h; simp [h] at ht
          apply hstrict t ht1
          intro u _ hne huF
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact absurd (hu1min u huF) (not_le.2 hlt)
          · exact hG ⟨u, Finset.mem_filter.2 ⟨huF, hgt⟩⟩
    obtain ⟨E, hE0, hE1, hE2⟩ := hdir
    have hev1 := key E hE1 hE2
    have hev2 := key (-E) (fun u hu => hE1 u (by simpa using hu))
      (fun t ht => hE2 t (by
        simp only [Pi.neg_apply, Finset.sum_neg_distrib, ne_eq, neg_eq_zero] at ht
        exact ht))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
    have hmem := hball (y := δ / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    obtain ⟨h1, h2⟩ := hmem
    have hseg : y ∈ openSegment ℝ (y + (δ / 2) • E) (y + (δ / 2) • -E) :=
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
        ext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring⟩
    have := hy.2 h1 h2 hseg
    have hD0 : (δ / 2) • E = 0 := by
      have := congrArg (fun z => z - y) this; simpa using this
    apply hE0
    rcases smul_eq_zero.1 hD0 with h | h
    · linarith
    · exact h
  refine ⟨hbin, fun t => ?_⟩
  have h1 := hk t
  have h2 : (∑ u ∈ Finset.Iic t, d u) / C ≤ ((⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) : ℝ) :=
    Int.le_ceil _
  have h3 := le_trans h2 h1
  rw [div_le_iff₀ hC] at h3
  linarith

theorem main {n : ℕ} (C : ℝ) (hC : 0 < C) (d : Fin n → ℝ) :
    convexHull ℝ (Lset C d) = Rset C d := by
  apply le_antisymm
  · exact convexHull_min (L_sub_R C hC d) (R_convex C d)
  · rw [← closure_convexHull_extremePoints (R_compact C d) (R_convex C d)]
    have hcl : IsClosed (convexHull ℝ (Lset C d)) := (L_finite C d).isClosed_convexHull ℝ
    apply closure_minimal _ hcl
    exact convexHull_mono (ext_sub_L C hC d)

end S226P_fdae2afc

theorem solution {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C)
    (hfeas : ({y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} : Set _).Nonempty) :
    convexHull ℝ {y : Fin n → ℝ | (∀ u, y u = 0 ∨ y u = 1) ∧
      ∀ t, (∑ u ∈ Finset.Iic t, d u) ≤ C * ∑ u ∈ Finset.Iic t, y u} =
    {y : Fin n → ℝ | (∀ u, 0 ≤ y u ∧ y u ≤ 1) ∧
      ∀ t, (⌈(∑ u ∈ Finset.Iic t, d u) / C⌉ : ℤ) ≤
        (∑ u ∈ Finset.Iic t, y u)} :=
  S226P_fdae2afc.main C hC d
