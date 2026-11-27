-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.proposition_L_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:43:25.749053+00:00
-- url     : https://prove2.me/submissions/b1f53daf-475b-49db-aa18-ef4c3157967a

import Definitions.Def_ProcureAssort_Hotelling_Supplement_CommonHotelling

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 2 ≤ n) (S : Finset ℝ) (f : ℝ → ℝ)
    (hTypes : ValidTypes (fun _ : Fin n => S) (fun _ => f))
    (hReg : Regular (fun _ : Fin n => S) (fun _ => f)) (delta : ℝ) (hdelta : 0 < delta)
    (a : Profile (fun _ : Fin n => S) → Fin n → ℝ) (b : Fin n → ℝ → ℝ)
    (hDep : RowDependence (fun _ : Fin n => f)
      (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (xstar (fun _ => S) (fun _ => f) (equiLoc n) delta)
      (fun θ => differenceA (activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ)) a b) :
    ∀ c ∈ S,
      virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0,by omega⟩ (S.max' (hTypes.1 ⟨0,by omega⟩)) -
        virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0,by omega⟩ c ≥ delta / (n-1 : ℕ) →
      ∀ i, b i c = 0 := by
        classical
        intro c hc hgap
        -- sum identity
        have hsum : ∀ θ : Profile (fun _ : Fin n => S),
            ∑ j, b j (θ j) * probOthers (fun _ : Fin n => f) j θ *
              xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j = 0 := by
          intro θ
          set Q := activeSet (fun _ => S) (fun _ => f) (equiLoc n) delta θ with hQ
          have h1 : ∑ j ∈ Q, ((∑ r ∈ Q.filter (fun r => ReducedRow Q r), a θ r * differenceA Q r j) +
              b j (θ j) * probOthers (fun _ : Fin n => f) j θ *
                xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j) = 0 :=
            Finset.sum_eq_zero (fun j hj => hDep θ j hj)
          rw [Finset.sum_add_distrib, Finset.sum_comm] at h1
          have h2 : ∑ r ∈ Q.filter (fun r => ReducedRow Q r), ∑ j ∈ Q, a θ r * differenceA Q r j = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            rw [← Finset.mul_sum]
            have hr' := (Finset.mem_filter.mp hr).2
            have hne : (Q.filter (r < ·)).Nonempty := by
              obtain ⟨_, j, hj, hrj⟩ := hr'
              exact ⟨j, Finset.mem_filter.mpr ⟨hj, hrj⟩⟩
            have hmem : (Q.filter (r < ·)).min' hne ∈ Q := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
            have : ∑ j ∈ Q, differenceA Q r j = 0 := by
              unfold differenceA
              simp only [dif_pos hne]
              rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Q, Finset.sum_ite_eq' Q, if_pos hmem, if_pos hr'.1]
              ring
            rw [this, mul_zero]
          rw [h2, zero_add] at h1
          rw [← h1]
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have : xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j = 0 := by
            unfold xstar hotDemand
            exact if_neg hj
          rw [this, mul_zero]
        have hNpos : (0:ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n-1)
        set N : ℝ := ((n-1 : ℕ) : ℝ) with hN
        have hNn : N = (n:ℝ) - 1 := by rw [hN, Nat.cast_sub (by omega)]; simp
        have hℓ : ∀ j : Fin n, equiLoc n j = (j.val : ℝ) / N := fun j => rfl
        have hmaxL : ∀ (Q : Finset (Fin n)) (j L : Fin n) (h : (Q.filter (· < j)).Nonempty),
            L ∈ Q → L < j → (∀ m ∈ Q, m < j → m ≤ L) → (Q.filter (· < j)).max' h = L := by
          intro Q j L h hL hLj hmax
          apply le_antisymm
          · apply Finset.max'_le; intro m hm; rw [Finset.mem_filter] at hm; exact hmax m hm.1 hm.2
          · exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hL, hLj⟩)
        have hminR : ∀ (Q : Finset (Fin n)) (j R : Fin n) (h : (Q.filter (j < ·)).Nonempty),
            R ∈ Q → j < R → (∀ m ∈ Q, j < m → R ≤ m) → (Q.filter (j < ·)).min' h = R := by
          intro Q j R h hR hjR hmin
          apply le_antisymm
          · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hR, hjR⟩)
          · apply Finset.le_min'; intro m hm; rw [Finset.mem_filter] at hm; exact hmin m hm.1 hm.2
        have hDem : ∀ (p : Fin n → ℝ) (j : Fin n) (lv rv : ℝ), j ∈ hotQ (equiLoc n) delta p →
            (if h : ((hotQ (equiLoc n) delta p).filter (· < j)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (· < j)).max' h) - p j
                + delta * |equiLoc n j - equiLoc n (((hotQ (equiLoc n) delta p).filter (· < j)).max' h)|) / (2 * delta)
            else equiLoc n j) = lv →
            (if h : ((hotQ (equiLoc n) delta p).filter (j < ·)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - p j
                + delta * |equiLoc n (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - equiLoc n j|) / (2 * delta)
            else 1 - equiLoc n j) = rv →
            hotDemand (equiLoc n) delta p j = lv + rv := by
          intro p j lv rv hj hl hr
          unfold hotDemand
          rw [if_pos hj, hl, hr]
        have hLeft : ∀ (p : Fin n → ℝ) (j L : Fin n), L ∈ hotQ (equiLoc n) delta p → L < j →
            (∀ m ∈ hotQ (equiLoc n) delta p, m < j → m ≤ L) →
            (if h : ((hotQ (equiLoc n) delta p).filter (· < j)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (· < j)).max' h) - p j
                + delta * |equiLoc n j - equiLoc n (((hotQ (equiLoc n) delta p).filter (· < j)).max' h)|) / (2 * delta)
            else equiLoc n j) = (p L - p j + delta * (((j.val:ℝ) - L.val) / N)) / (2 * delta) := by
          intro p j L hL hLj hmax
          have hne : ((hotQ (equiLoc n) delta p).filter (· < j)).Nonempty :=
            ⟨L, Finset.mem_filter.mpr ⟨hL, hLj⟩⟩
          rw [dif_pos hne, hmaxL _ j L hne hL hLj hmax, hℓ, hℓ, ← sub_div, abs_of_nonneg]
          apply div_nonneg _ hNpos.le
          have : (L.val:ℝ) < j.val := by exact_mod_cast hLj
          linarith
        have hLeftNone : ∀ (p : Fin n → ℝ) (j : Fin n), (∀ m ∈ hotQ (equiLoc n) delta p, ¬ m < j) →
            (if h : ((hotQ (equiLoc n) delta p).filter (· < j)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (· < j)).max' h) - p j
                + delta * |equiLoc n j - equiLoc n (((hotQ (equiLoc n) delta p).filter (· < j)).max' h)|) / (2 * delta)
            else equiLoc n j) = (j.val : ℝ) / N := by
          intro p j hno
          have hne : ¬ ((hotQ (equiLoc n) delta p).filter (· < j)).Nonempty := by
            rintro ⟨m, hm⟩
            rw [Finset.mem_filter] at hm
            exact hno m hm.1 hm.2
          rw [dif_neg hne, hℓ]
        have hRight : ∀ (p : Fin n → ℝ) (j R : Fin n), R ∈ hotQ (equiLoc n) delta p → j < R →
            (∀ m ∈ hotQ (equiLoc n) delta p, j < m → R ≤ m) →
            (if h : ((hotQ (equiLoc n) delta p).filter (j < ·)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - p j
                + delta * |equiLoc n (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - equiLoc n j|) / (2 * delta)
            else 1 - equiLoc n j) = (p R - p j + delta * (((R.val:ℝ) - j.val) / N)) / (2 * delta) := by
          intro p j R hR hjR hmin
          have hne : ((hotQ (equiLoc n) delta p).filter (j < ·)).Nonempty :=
            ⟨R, Finset.mem_filter.mpr ⟨hR, hjR⟩⟩
          rw [dif_pos hne, hminR _ j R hne hR hjR hmin, hℓ, hℓ, ← sub_div, abs_of_nonneg]
          apply div_nonneg _ hNpos.le
          have : (j.val:ℝ) < R.val := by exact_mod_cast hjR
          linarith
        have hRightNone : ∀ (p : Fin n → ℝ) (j : Fin n), (∀ m ∈ hotQ (equiLoc n) delta p, ¬ j < m) →
            (if h : ((hotQ (equiLoc n) delta p).filter (j < ·)).Nonempty then
              (p (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - p j
                + delta * |equiLoc n (((hotQ (equiLoc n) delta p).filter (j < ·)).min' h) - equiLoc n j|) / (2 * delta)
            else 1 - equiLoc n j) = 1 - (j.val : ℝ) / N := by
          intro p j hno
          have hne : ¬ ((hotQ (equiLoc n) delta p).filter (j < ·)).Nonempty := by
            rintro ⟨m, hm⟩
            rw [Finset.mem_filter] at hm
            exact hno m hm.1 hm.2
          rw [dif_neg hne, hℓ]
        -- constant prices
        have hA : ∀ (V : ℝ) (j : Fin n), hotDemand (equiLoc n) delta (fun _ => V) j =
            ((if 0 < j.val then (1:ℝ) else 0) + (if j.val + 1 < n then (1:ℝ) else 0)) / (2 * N) := by
          intro V j
          have hall : ∀ m, m ∈ hotQ (equiLoc n) delta (fun _ => V) := by
            intro m
            simp only [hotQ, Finset.mem_filter, Finset.mem_univ, true_and, sub_self]
            intro k; positivity
          have hpos2 : (0:ℝ) < 2 * delta := by linarith
          rw [hDem _ j ((if 0 < j.val then (1:ℝ) else 0) / (2*N))
            ((if j.val + 1 < n then (1:ℝ) else 0) / (2*N)) (hall j)]
          · ring
          · by_cases h0 : 0 < j.val
            · rw [if_pos h0, hLeft _ j ⟨j.val - 1, by omega⟩ (hall _) (by rw [Fin.lt_def]; simp; omega)
                (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega)]
              have : ((⟨j.val - 1, by omega⟩ : Fin n).val : ℝ) = (j.val : ℝ) - 1 := by
                simp only; rw [Nat.cast_sub (by omega)]; simp
              rw [this]; field_simp; ring
            · rw [if_neg h0, hLeftNone _ j (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
              have : j.val = 0 := by omega
              simp [this]
          · by_cases h1 : j.val + 1 < n
            · rw [if_pos h1, hRight _ j ⟨j.val + 1, by omega⟩ (hall _) (by rw [Fin.lt_def]; simp)
                (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega)]
              have : ((⟨j.val + 1, by omega⟩ : Fin n).val : ℝ) = (j.val : ℝ) + 1 := by
                simp
              rw [this]; field_simp; ring
            · rw [if_neg h1, hRightNone _ j (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
              have : (j.val : ℝ) = N := by
                rw [hN]; exact_mod_cast (by omega : j.val = n - 1)
              rw [this, div_self hNpos.ne']; simp
        have hB : ∀ (V D : ℝ), delta / N ≤ D → ∀ (k j : Fin n),
            hotDemand (equiLoc n) delta (fun m => if m = k then V + D else V) j =
            if j = k then 0 else
              ((if 0 < j.val then (1:ℝ) else 0) + (if j.val = k.val + 1 then (1:ℝ) else 0)) / (2 * N) +
              ((if j.val + 1 < n then (1:ℝ) else 0) + (if j.val + 1 = k.val then (1:ℝ) else 0)) / (2 * N) := by
          intro V D hD k j
          have hDpos : 0 < D := lt_of_lt_of_le (div_pos hdelta hNpos) hD
          have hpos2 : (0:ℝ) < 2 * delta := by linarith
          have hmem : ∀ m, m ≠ k → m ∈ hotQ (equiLoc n) delta (fun m => if m = k then V + D else V) := by
            intro m hm
            simp only [hotQ, Finset.mem_filter, Finset.mem_univ, true_and]
            intro m'
            rw [if_neg hm]
            have : 0 ≤ delta * |equiLoc n m' - equiLoc n m| := by positivity
            split_ifs <;> linarith
          have hkQ : k ∈ hotQ (equiLoc n) delta (fun m => if m = k then V + D else V) → D = delta / N := by
            intro hk
            simp only [hotQ, Finset.mem_filter, Finset.mem_univ, true_and] at hk
            apply le_antisymm _ hD
            by_cases hk1 : k.val + 1 < n
            · have := hk ⟨k.val + 1, hk1⟩
              have hne : (⟨k.val + 1, hk1⟩ : Fin n) ≠ k := by intro h; rw [Fin.ext_iff] at h; simp at h
              rw [if_pos trivial, if_neg hne, hℓ, hℓ, ← sub_div] at this
              have hc : ((⟨k.val + 1, hk1⟩ : Fin n).val : ℝ) = (k.val:ℝ) + 1 := by simp
              rw [hc, show ((k.val:ℝ) + 1 - k.val) = 1 by ring,
                abs_of_pos (by positivity : (0:ℝ) < 1 / N)] at this
              have : delta * (1 / N) = delta / N := by ring
              linarith
            · have hk0 : 0 < k.val := by omega
              have := hk ⟨k.val - 1, by omega⟩
              have hne : (⟨k.val - 1, by omega⟩ : Fin n) ≠ k := by
                intro h; rw [Fin.ext_iff] at h; simp at h; omega
              rw [if_pos trivial, if_neg hne, hℓ, hℓ, ← sub_div] at this
              have hc : ((⟨k.val - 1, by omega⟩ : Fin n).val : ℝ) = (k.val:ℝ) - 1 := by
                simp only; rw [Nat.cast_sub (by omega)]; simp
              rw [hc, show ((k.val:ℝ) - 1 - k.val) = -1 by ring, neg_div, abs_neg,
                abs_of_pos (by positivity : (0:ℝ) < 1 / N)] at this
              have : delta * (1 / N) = delta / N := by ring
              linarith
          have hpk : (if k = k then V + D else V) = V + D := by simp
          have hpo : ∀ m, m ≠ k → (if m = k then V + D else V) = V := by
            intro m hm; simp [hm]
          have hcm1 : ∀ (m : Fin n) (h : m.val - 1 < n), 0 < m.val →
              ((⟨m.val - 1, h⟩ : Fin n).val : ℝ) = (m.val : ℝ) - 1 := by
            intro m h h0; simp only; rw [Nat.cast_sub (by omega)]; simp
          have hcp1 : ∀ (m : Fin n) (h : m.val + 1 < n),
              ((⟨m.val + 1, h⟩ : Fin n).val : ℝ) = (m.val : ℝ) + 1 := by
            intro m h; simp
          by_cases hjk : j = k
          · rw [if_pos hjk, hjk]
            by_cases hk : k ∈ hotQ (equiLoc n) delta (fun m => if m = k then V + D else V)
            · have hDe := hkQ hk
              rw [hDem _ k 0 0 hk]
              · ring
              · by_cases h0 : 0 < k.val
                · have hne : (⟨k.val - 1, by omega⟩ : Fin n) ≠ k := by
                    intro h; rw [Fin.ext_iff] at h; simp at h; omega
                  rw [hLeft _ k ⟨k.val - 1, by omega⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp; omega)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega),
                    hpk, hpo _ hne, hcm1 k (by omega) h0, hDe]
                  field_simp; ring
                · rw [hLeftNone _ k (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
                  have : k.val = 0 := by omega
                  simp [this]
              · by_cases h1 : k.val + 1 < n
                · have hne : (⟨k.val + 1, h1⟩ : Fin n) ≠ k := by
                    intro h; rw [Fin.ext_iff] at h; simp at h
                  rw [hRight _ k ⟨k.val + 1, h1⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega),
                    hpk, hpo _ hne, hcp1 k h1, hDe]
                  field_simp; ring
                · rw [hRightNone _ k (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
                  have : (k.val : ℝ) = N := by
                    rw [hN]; exact_mod_cast (by omega : k.val = n - 1)
                  rw [this, div_self hNpos.ne']; simp
            · unfold hotDemand; exact if_neg hk
          · rw [if_neg hjk]
            have hjv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
            rw [hDem _ j (((if 0 < j.val then (1:ℝ) else 0) + (if j.val = k.val + 1 then (1:ℝ) else 0)) / (2 * N))
              (((if j.val + 1 < n then (1:ℝ) else 0) + (if j.val + 1 = k.val then (1:ℝ) else 0)) / (2 * N))
              (hmem j hjk)]
            · -- left part
              by_cases h0 : j.val = 0
              · rw [hLeftNone _ j (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
                simp [h0]
              by_cases h1 : j.val = k.val + 1
              · rw [if_pos (by omega : 0 < j.val), if_pos h1]
                by_cases hk : k ∈ hotQ (equiLoc n) delta (fun m => if m = k then V + D else V)
                · have hDe := hkQ hk
                  rw [hLeft _ j k hk (by rw [Fin.lt_def]; omega)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; omega),
                    hpk, hpo _ hjk, hDe]
                  have : (j.val : ℝ) = k.val + 1 := by exact_mod_cast h1
                  rw [this]; field_simp; ring
                by_cases hk0 : k.val = 0
                · rw [hLeftNone _ j (fun m hm hmj => by
                    rw [Fin.lt_def] at hmj
                    have : m = k := Fin.ext (by omega)
                    exact hk (this ▸ hm))]
                  have : (j.val : ℝ) = 1 := by exact_mod_cast (by omega : j.val = 1)
                  rw [this]; field_simp; ring
                · have hne : (⟨k.val - 1, by omega⟩ : Fin n) ≠ k := by
                    intro h; rw [Fin.ext_iff] at h; simp at h; omega
                  rw [hLeft _ j ⟨k.val - 1, by omega⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp; omega)
                    (fun m hm hmj => by
                      rw [Fin.lt_def] at hmj; rw [Fin.le_def]; simp
                      have : m ≠ k := fun h => hk (h ▸ hm)
                      have : m.val ≠ k.val := fun h => this (Fin.ext h)
                      omega),
                    hpo _ hne, hpo _ hjk, hcm1 k (by omega) (by omega)]
                  have : (j.val : ℝ) = k.val + 1 := by exact_mod_cast h1
                  rw [this]; field_simp; ring
              · have hne : (⟨j.val - 1, by omega⟩ : Fin n) ≠ k := by
                  intro h; rw [Fin.ext_iff] at h; simp at h; omega
                rw [if_pos (by omega : 0 < j.val), if_neg h1,
                  hLeft _ j ⟨j.val - 1, by omega⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp; omega)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega),
                  hpo _ hne, hpo _ hjk, hcm1 j (by omega) (by omega)]
                field_simp; ring
            · -- right part
              by_cases h0 : j.val + 1 = n
              · rw [hRightNone _ j (fun m _ hm => by rw [Fin.lt_def] at hm; omega)]
                have : (j.val : ℝ) = N := by
                  rw [hN]; exact_mod_cast (by omega : j.val = n - 1)
                rw [this, div_self hNpos.ne']
                have h2 : ¬ (j.val + 1 = k.val) := by omega
                rw [if_neg (by omega : ¬ j.val + 1 < n), if_neg h2]; simp
              by_cases h1 : j.val + 1 = k.val
              · rw [if_pos (by omega : j.val + 1 < n), if_pos h1]
                by_cases hk : k ∈ hotQ (equiLoc n) delta (fun m => if m = k then V + D else V)
                · have hDe := hkQ hk
                  rw [hRight _ j k hk (by rw [Fin.lt_def]; omega)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; omega),
                    hpk, hpo _ hjk, hDe]
                  have : (k.val : ℝ) = j.val + 1 := by exact_mod_cast h1.symm
                  rw [this]; field_simp; ring
                by_cases hk0 : k.val + 1 = n
                · rw [hRightNone _ j (fun m hm hmj => by
                    rw [Fin.lt_def] at hmj
                    have : m = k := Fin.ext (by omega)
                    exact hk (this ▸ hm))]
                  have : (j.val : ℝ) = N - 1 := by
                    rw [hNn]; have : (j.val : ℝ) + 2 = n := by exact_mod_cast (by omega : j.val + 2 = n)
                    linarith
                  rw [this]; field_simp; ring
                · have hne : (⟨k.val + 1, by omega⟩ : Fin n) ≠ k := by
                    intro h; rw [Fin.ext_iff] at h; simp at h
                  rw [hRight _ j ⟨k.val + 1, by omega⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp; omega)
                    (fun m hm hmj => by
                      rw [Fin.lt_def] at hmj; rw [Fin.le_def]; simp
                      have : m ≠ k := fun h => hk (h ▸ hm)
                      have : m.val ≠ k.val := fun h => this (Fin.ext h)
                      omega),
                    hpo _ hne, hpo _ hjk, hcp1 k (by omega)]
                  have : (k.val : ℝ) = j.val + 1 := by exact_mod_cast h1.symm
                  rw [this]; field_simp; ring
              · have hne : (⟨j.val + 1, by omega⟩ : Fin n) ≠ k := by
                  intro h; rw [Fin.ext_iff] at h; simp at h; omega
                rw [if_pos (by omega : j.val + 1 < n), if_neg h1,
                  hRight _ j ⟨j.val + 1, by omega⟩ (hmem _ hne) (by rw [Fin.lt_def]; simp)
                    (fun m _ hm => by rw [Fin.lt_def] at hm; rw [Fin.le_def]; simp; omega),
                  hpo _ hne, hpo _ hjk, hcp1 j (by omega)]
                field_simp; ring
        -- reduce the sum identity to profiles of c and max types
        have hred : ∀ θ : Profile (fun _ : Fin n => S),
            (∀ j, (θ j : ℝ) ≠ c → xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j = 0) →
            ∑ j, b j c * xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j = 0 := by
          intro θ hθ
          have hP : ∀ j, probOthers (fun _ : Fin n => f) j θ * f (θ j) = prob (fun _ : Fin n => f) θ := by
            intro j; unfold probOthers prob; exact Finset.prod_erase_mul _ _ (Finset.mem_univ j)
          have hprob : 0 < prob (fun _ : Fin n => f) θ :=
            Finset.prod_pos (fun j _ => hTypes.2.2.1 j _ (θ j).2)
          have hfc : 0 < f c := hTypes.2.2.1 ⟨0, by omega⟩ c hc
          have key : (∑ j, b j c * xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j) *
              prob (fun _ : Fin n => f) θ =
              (∑ j, b j (θ j) * probOthers (fun _ : Fin n => f) j θ *
                xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θ j) * f c := by
            rw [Finset.sum_mul, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : (θ j : ℝ) = c
            · rw [← hP j, hj]; ring
            · rw [hθ j hj]; ring
          rw [hsum θ, zero_mul] at key
          exact (mul_eq_zero.mp key).resolve_right hprob.ne'
        set M := S.max' (hTypes.1 ⟨0, by omega⟩) with hMdef
        have hMS : M ∈ S := Finset.max'_mem _ _
        set vc := virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0, by omega⟩ c with hvc
        set D := virtualCost (fun _ : Fin n => S) (fun _ => f) ⟨0, by omega⟩ M - vc with hDdef
        have hD : delta / N ≤ D := hgap
        obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun j => b j c := ⟨_, rfl⟩
        obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = fun j =>
            ((if 0 < j.val then (1:ℝ) else 0) + (if j.val + 1 < n then (1:ℝ) else 0)) / (2 * N) := ⟨_, rfl⟩
        -- all-c profile
        have E0 : ∑ j, y j * w j = 0 := by
          have := hred (fun _ => ⟨c, hc⟩) (fun j hj => absurd rfl hj)
          rw [← this]
          apply Finset.sum_congr rfl
          intro j _
          rw [hy, hw]
          unfold xstar
          have hv : vvec (fun _ : Fin n => S) (fun _ => f) (fun _ => ⟨c, hc⟩) = fun _ => vc := by
            funext m; rfl
          rw [hv, hA]
        -- one-max profiles
        have Ek : ∀ k : Fin n, ∑ j, y j * (if j = k then 0 else
              ((if 0 < j.val then (1:ℝ) else 0) + (if j.val = k.val + 1 then (1:ℝ) else 0)) / (2 * N) +
              ((if j.val + 1 < n then (1:ℝ) else 0) + (if j.val + 1 = k.val then (1:ℝ) else 0)) / (2 * N)) = 0 := by
          intro k
          let θk : Profile (fun _ : Fin n => S) := fun j => if j = k then ⟨M, hMS⟩ else ⟨c, hc⟩
          have hv : vvec (fun _ : Fin n => S) (fun _ => f) θk = fun m => if m = k then vc + D else vc := by
            funext m
            by_cases h : m = k
            · simp only [vvec, θk, if_pos h]
              rw [hDdef, add_sub_cancel]; rfl
            · simp only [vvec, θk, if_neg h]; rfl
          have hx : ∀ j, xstar (fun _ => S) (fun _ => f) (equiLoc n) delta θk j =
              (if j = k then 0 else
              ((if 0 < j.val then (1:ℝ) else 0) + (if j.val = k.val + 1 then (1:ℝ) else 0)) / (2 * N) +
              ((if j.val + 1 < n then (1:ℝ) else 0) + (if j.val + 1 = k.val then (1:ℝ) else 0)) / (2 * N)) := by
            intro j; unfold xstar; rw [hv, hB vc D hD k j]
          have := hred θk (fun j hj => by
            have hjk : j = k := by
              by_contra h
              simp only [θk, if_neg h] at hj
              exact hj rfl
            rw [hx, if_pos hjk])
          refine Eq.trans ?_ this
          apply Finset.sum_congr rfl
          intro j _
          rw [hy, hx]
        have h2N : (0:ℝ) < 2 * N := by linarith
        have hR : ∀ k : Fin n,
            (if hk : k.val + 1 < n then y ⟨k.val + 1, hk⟩ else 0) +
              (if hk : 0 < k.val then y ⟨k.val - 1, by omega⟩ else 0) =
            ((if 0 < k.val then (1:ℝ) else 0) + (if k.val + 1 < n then (1:ℝ) else 0)) * y k := by
          intro k
          have h1 : (∑ j, y j * (if j = k then 0 else
              ((if 0 < j.val then (1:ℝ) else 0) + (if j.val = k.val + 1 then (1:ℝ) else 0)) / (2 * N) +
              ((if j.val + 1 < n then (1:ℝ) else 0) + (if j.val + 1 = k.val then (1:ℝ) else 0)) / (2 * N)))
              - ∑ j, y j * w j =
              (∑ j, y j * (if j.val = k.val + 1 then (1:ℝ) else 0) / (2 * N)) +
              (∑ j, y j * (if j.val + 1 = k.val then (1:ℝ) else 0) / (2 * N)) -
              ∑ j, (if j = k then y k * w k else 0) := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hjk : j = k
            · subst hjk
              rw [if_pos rfl, if_pos rfl, if_neg (by omega), if_neg (by omega)]
              ring
            · rw [if_neg hjk, if_neg hjk, hw]
              ring
          have hs1 : (∑ j, y j * (if j.val = k.val + 1 then (1:ℝ) else 0) / (2 * N)) =
              (if hk : k.val + 1 < n then y ⟨k.val + 1, hk⟩ else 0) / (2 * N) := by
            rw [← Finset.sum_div]
            congr 1
            split_ifs with hk
            · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩]
              · simp
              · intro j _ hj
                rw [if_neg (fun h => hj (Fin.ext h)), mul_zero]
              · intro h; exact absurd (Finset.mem_univ _) h
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega), mul_zero]
          have hs2 : (∑ j, y j * (if j.val + 1 = k.val then (1:ℝ) else 0) / (2 * N)) =
              (if hk : 0 < k.val then y ⟨k.val - 1, by omega⟩ else 0) / (2 * N) := by
            rw [← Finset.sum_div]
            congr 1
            split_ifs with hk
            · rw [Finset.sum_eq_single ⟨k.val - 1, by omega⟩]
              · rw [if_pos (by simp; omega), mul_one]
              · intro j _ hj
                rw [if_neg (fun h => hj (Fin.ext (by simp; omega))), mul_zero]
              · intro h; exact absurd (Finset.mem_univ _) h
            · apply Finset.sum_eq_zero
              intro j _
              rw [if_neg (by omega), mul_zero]
          rw [Ek k, E0, sub_zero, hs1, hs2, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ _),
            hw] at h1
          field_simp at h1
          linarith
        have hstep : ∀ m (hm : m + 1 < n), y ⟨m + 1, hm⟩ = y ⟨m, by omega⟩ := by
          intro m
          induction m with
          | zero =>
            intro hm
            have := hR ⟨0, by omega⟩
            simp only at this
            rw [dif_pos hm, dif_neg (lt_irrefl 0), if_neg (lt_irrefl 0), if_pos hm] at this
            linarith
          | succ m ih =>
            intro hm
            have := hR ⟨m + 1, by omega⟩
            simp only at this
            rw [dif_pos hm, dif_pos (by omega), if_pos (by omega), if_pos (by omega)] at this
            have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
            rw [e] at this
            have ih' := ih (by omega)
            linarith
        have hall : ∀ m (hm : m < n), y ⟨m, hm⟩ = y ⟨0, by omega⟩ := by
          intro m
          induction m with
          | zero => intro _; rfl
          | succ m ih => intro hm; rw [hstep m hm, ih]
        have hwnn : ∀ j, 0 ≤ w j := by
          intro j; rw [hw]
          apply div_nonneg _ h2N.le
          apply add_nonneg <;> split_ifs <;> norm_num
        have hw0 : 0 < w ⟨0, by omega⟩ := by
          rw [hw]; simp only [lt_irrefl, if_false, zero_add]
          rw [if_pos (by omega)]; positivity
        have hsw : 0 < ∑ j, w j :=
          lt_of_lt_of_le hw0 (Finset.single_le_sum (fun j _ => hwnn j) (Finset.mem_univ _))
        have hy0 : y ⟨0, by omega⟩ = 0 := by
          have : ∑ j, y j * w j = y ⟨0, by omega⟩ * ∑ j, w j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [show y j = y ⟨j.val, j.isLt⟩ from rfl, hall j.val j.isLt]
          rw [this] at E0
          exact (mul_eq_zero.mp E0).resolve_right hsw.ne'
        intro i
        have : b i c = y i := by rw [hy]
        rw [this, show y i = y ⟨i.val, i.isLt⟩ from rfl, hall i.val i.isLt, hy0]
